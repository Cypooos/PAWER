use crate::definitions::*;
use crate::errors::*;
use crate::parsing;
use std::collections::{HashMap, HashSet};
use std::fmt;

// This file contains all functions that act on the `GlobalContext` object
// This include all commands, tactics, and optimisation functions

type InductiveConstrDef = (VariableName /* le_refl */, LambdaTerm /* forall x:nat, le x x */);
type InductiveParams = (VariableName /* name */, LambdaTerm /* type */);


// The list of implemented commands. See the readme for more informations
#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Command {
    Check(LambdaTerm),
    Reduce(LambdaTerm),
    Tactic(Tactic),
    Print(LambdaTerm),
    Goal(LambdaTerm),
    Theorem(VariableName, LambdaTerm), // Theorem(name, propriety)
    Definition(VariableName, LambdaTerm), // Definition(name, lambda-term)
    Qed,
    Cancel,
    Search(String),
    PrintProof,
    Clean, // clean the state by freeing the memory. Doesn't work yet.

    /// Create an inductive type/object. Inductive(name, inductive parameters, arity, list of constructors)
    Inductive(VariableName, Vec<InductiveParams>, LambdaTerm, Vec<InductiveConstrDef>),
}

impl fmt::Display for Command {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::Check(l) => write!(f, "Check {l}"),
            Self::Reduce(l) => write!(f, "Reduce {l}"),
            Self::Tactic(l) => write!(f, "{l}"),
            Self::Goal(li) => write!(f,"Goal {li}"),
            Self::Theorem(name,e) => write!(f, "Theorem {}: {e}", var_to_string(name)),
            Self::Definition(name,e) => write!(f, "Definition {}: {e}", var_to_string(name)),
            Self::Cancel => write!(f, "Cancel"),
            Self::Qed => write!(f, "Qed"),
            Self::Inductive(..) => write!(f, "Inductive (todo...)"),
            Self::Print(l) => write!(f, "Print {l}"),
            Self::Search(t) => write!(f, "Search {t}"),
            Self::PrintProof => write!(f, "PrintProof"),
            Self::Clean => write!(f, "Clean"),

        }
    }
}

// The list of implemented tactics. See README.md
#[derive(Debug, Eq, Clone, PartialEq)]
pub enum Tactic {
    Apply(LambdaTerm),
    Exact(LambdaTerm),
    Cut(LambdaTerm),
    Intros(Vec<VariableName>),
    Intro(Option<VariableName>),
    Unfold(VariableName),
    Simpl,
    Induction(VariableName),
}

impl fmt::Display for Tactic {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::Apply(l) => write!(f, "apply {}", l),
            Self::Exact(l) => write!(f, "exact {}", l),
            Self::Cut(l) => write!(f, "cut {}", l),
            Self::Intros(li) => write!(
                f,
                "intros {}",
                li.iter()
                    .map(var_to_string)
                    .collect::<Vec<String>>()
                    .join(" ")
            ),
            Self::Intro(Some(e)) => write!(f, "intro {}", var_to_string(e)),
            Self::Intro(None) => write!(f, "intro"),
            Self::Unfold(name) => write!(f, "unfold {}",var_to_string(name)),
            Self::Simpl => write!(f,"simpl"),
            Self::Induction(n) => write!(f,"induction {}",var_to_string(n))
        }
    }
}

#[allow(dead_code, unused_variables)]
impl GlobalContext {

    /// Execute a single command, returning either the sucess message as a String or an Error
    /// Most commands have their own functions, see below
    pub fn command(&mut self, comm: Command) -> Result<String, Error> {
        match comm {
            Command::Qed => self.qed(),
            Command::Clean => Ok(format!("Freed {} pointors.",self.clean()?)),
            Command::Goal(l) => self.set_goal(l),
            Command::Theorem(name, lam) => {
                match self.constants.get(&name) { // check that a constant of the same name doesn't already exist
                    Some(term) => {
                        let str = self.lambda_to_string(term.1);
                        Err(Error::EvaluationError(EvaluationError::TheoremAlreadyExists(var_to_string(&name), str)))
                    },
                    None => self.set_goal_named(lam, name)
                }
            },
            Command::Check(lamb) => self.check(lamb.clone()),
            Command::Reduce(lamb) => self.reduce(lamb.clone()),
            Command::Tactic(tact) => self.tactic(tact),
            Command::Definition(name,obj) => self.define(name.clone(),obj).map(|()|format!("`{}` is defined.",var_to_string(&name))),
            Command::Cancel => self.reset()
                .map(|()|format!("Proof resetted."))
                .map_err(|x|Error::InternalError(x)),
            Command::Inductive(name, params, arity, constructors) => {
                self.add_inductive(name, params, arity, constructors)
            }
            Command::Print(l) => {
                let node = self.insert_term(l)?;
                let out = format!("Lambda is `{}`",self.lambda_to_string(node));
                Ok(out)
            }
            Command::PrintProof => {
                match &self.root {
                    None => return Err(EvaluationError::NoProof.into()),
                    Some(e) => return Ok(format!("Proof is {}",self.lambda_to_string(e.root))),
                }
            }
            Command::Search(t) => {
                let mut constant_res = self.constants.iter().map(
                    |(k,(def,tp))| {
                        let d = self.lambda_to_string(*def);
                        if d.len() < 50 {
                            format!("{}\t: {} := {}.",var_to_string(&k),self.lambda_to_string(*tp),d)
                        } else {
                            format!("{}\t: {}\n  \t:= {}.",var_to_string(&k),self.lambda_to_string(*tp),d)
                        }
                    }
                ).filter(|str| str.contains(&t))
                .collect::<Vec<String>>();
                constant_res.sort();
                let constant_res = constant_res.join("\n");

                let mut inductive_res = self.inductives.iter().map(|(j,_)|self.inductive_to_string(j)).filter(|str| str.contains(&t)).collect::<Vec<String>>();
                inductive_res.sort();
                let inductive_res = inductive_res.join("\n");

                Ok(format!(" --- Inductives ---\n{}\n\n --- Functions / Def / Theorems ---\n{}",inductive_res,constant_res))
            }
        }
    }

    /// Execute a series of command, either returning the first Err(Error) or the output message of the last command 
    pub fn commands(&mut self, comms:Vec<Command>) -> Result<String, Error> {
        let mut last = "No commands executed.".to_owned();
        for comm in comms {
            match self.command(comm) {
                Ok(e) => last = e,
                Err(e) => return Err(e)
            }
        };
        return Ok(last)
    }

    /// Load the standard library into the GlobalContext
    pub fn load_prelude(&mut self) {
        self.exec_commands(&format!(include_str!("stdlib.v"),usize::MAX - 1)
        ).expect("Prelude doesn't work!");
    }

    /// Perform the `Check` command. Tries to type `lamb` using self.get_type
    pub fn check(&mut self, lamb: LambdaTerm) -> Result<String, Error> {
        let mut ctx = if self.goals.len() > 0 {
            self.goals[self.goals.len()-1].context
                .iter().map(|x| x.0.clone()).collect()
        } else {
            Vec::new()
        };
        let node_index = self.insert_term_ctx(lamb.clone(), &mut ctx)?;
        let mut ctx = if self.goals.len() > 0 {
            self.goals[self.goals.len()-1].context.clone()
        } else {
            Vec::new()
        };
        let t = self.get_type(&mut ctx, node_index).map_err(|x|Error::EvaluationError(EvaluationError::CheckComm(lamb,x)));
        t.map(|x| self.lambda_to_string_with_context(x, &mut ctx))
    }

    /// Perform the `Reduce` command. Tries to calculate a beta normal-form of `lamb` using self.beta_reduction
    pub fn reduce(&mut self, lamb: LambdaTerm) -> Result<String,Error> {
        let mut ctx = if self.goals.len() > 0 {
            self.goals[self.goals.len()-1].context
                .iter().map(|x| x.0.clone()).collect()
        } else {
            Vec::new()
        };
        let node_index = self.insert_term_ctx(lamb.clone(), &mut ctx)?;
        let mut ctx = if self.goals.len() > 0 {
            self.goals[self.goals.len()-1].context.clone()
        } else {
            Vec::new()
        };
        self.beta_reduction(node_index);
        Ok(format!("Reduce is {}",self.lambda_to_string_with_context(node_index, &mut ctx)))
    }

    /// Applies a tactic, returning the result to be displayed, as a String, if it sucessed
    pub fn tactic(&mut self, tact: Tactic) -> Result<String, Error> {
        if self.root == None { return Err(EvaluationError::NoProof.into()); }
        if self.goals.len() == 0 { // since a tactic can't be applied without any goals, we first check this
            return Err(EvaluationError::NoMoreGoals(tact).into());
        }
        match tact {
            Tactic::Exact(e) => self.tact_exact(e),
            Tactic::Intro(name) => self.tact_intro(name),
            Tactic::Intros(names) => self.tact_intros(names),
            Tactic::Apply(name) => self.tact_apply(name).map(|()| "".to_string()),
            Tactic::Unfold(name) => self.tact_unfold(name),
            Tactic::Simpl => self.tact_simpl().map(|()| "".to_string()),
            Tactic::Induction(var) => self.tact_induction(var),
            _ => Err(InternalError::UnimplementedTactic(tact).into()),
        }
    }

    // Perform a pass of beta reduction on the proof
    pub fn tact_simpl(&mut self) -> Result<(),Error> {
        if self.goals.len() > 0 {
            self.beta_reduction(self.goals[self.goals.len() - 1].goal);
            Ok(())
        } else {
            Err(EvaluationError::NoMoreGoals(Tactic::Simpl).into())
        }

    }

    /// method doing the tactic apply on the current goal.
    pub fn tact_apply(&mut self, lamb: LambdaTerm) -> Result<(), Error> {
        let curr = &mut match self.goals.get(self.goals.len()-1) {
            None => return Err(InternalError::NoMoreGoalsTactic("apply").into()),
            Some(x) => x.clone()
        };

        let mut _ctx = self.goals[self.goals.len()-1].context.iter().map(|x| x.0.clone()).collect::<Vec<VariableName>>();
        let mut current_hyp = self.insert_term_ctx(lamb,&mut _ctx)?;
        let /*mut*/ ctx = self.goals[self.goals.len()-1].context.clone();
        let mut current_type = self.get_type(&mut ctx.clone(), current_hyp).unwrap();

        let mut goals_to_push = vec![];

        loop {
            /*println!("CHECKING {} SUB OF {} -- HYP IS {} -- GOALS ARE {}",
                self.lambda_to_string_with_context(current_type, &mut ctx.clone()),
                self.lambda_to_string_with_context(curr.goal, &mut ctx.clone()),
                self.lambda_to_string_with_context(current_hyp, &mut ctx.clone()),
                goals_to_push.clone().iter().map(|x:&HoleContext|self.lambda_to_string_with_context(x.goal,&mut x.context.clone())).collect::<Vec<String>>().join(", ")
            );*/
            let new_goal = self.unfold_constants(curr.goal)?;
            let new_goal = self.deep_copy(new_goal);
            self.beta_reduction(new_goal);
            let new_type = self.unfold_constants(current_type)?;
            let new_type = self.deep_copy(new_type);
            self.beta_reduction(new_type);
            if self.subtype(&mut ctx.clone(),new_type,&mut ctx.clone(), new_goal).is_ok() {
                self.merge_term(current_hyp, curr.node);
                self.goals.pop();
                goals_to_push.reverse();
                self.goals.append(&mut goals_to_push);
                return Ok(())
            };
            match self.lambda_storage[current_type].clone() {
                LambdaNode::Pi(n,a,b) if !self.is_used_var(b) => {

                    let to_do = self.insert_node(LambdaNode::Hole);
                    self.shift_index_overwrite(-1, b);

                    current_hyp = self.insert_node(LambdaNode::App(current_hyp,to_do));

                    let mut hole_to_do = HoleContext::new(a,to_do);
                    hole_to_do.context = ctx.iter().map(|x|x.clone()).collect::<Vec<_>>();
                    goals_to_push.push(hole_to_do);

                    current_type = b;
                },
                _ => return Err(EvaluationError::ApplyGoalNotFound.into())
            }
        }
    }

    /// Perform the unfold tactic
    pub fn tact_unfold(&mut self, name:VariableName) -> Result<String,Error> {
        let curr = match self.goals.get(self.goals.len()-1) { // get the current goal
            None => return Err(InternalError::NoMoreGoalsTactic("unfold").into()),
            Some(x) => x
        };
        let (def,_) = match self.constants.get(&name) { // get the definition of `name` (if it exists)
            None => return Err(EvaluationError::UnfoldNotFound(var_to_string(&name)).into()),
            Some(e) => e
        }; 
        self.replace_const(curr.goal, &name, *def)?; Ok("".to_owned()) // replace
    }

    /// method doing the tactic intro on the current goal
    pub fn tact_intro(&mut self, opt_name: Option<VariableName>) -> Result<String, Error> {
        let curr = match self.goals.get(self.goals.len()-1) {
            None => return Err(InternalError::NoMoreGoalsTactic("intro").into()),
            Some(x) => x
        };
        match self.lambda_storage.get(curr.goal).clone() {
            None => Err(InternalError::NodeIncorrectPointer(curr.goal).into()),
            Some(LambdaNode::Pi(name, ty, body)) => {
                let name = match opt_name{
                    Some(n) => n,
                    None => name.clone()
                };
                let ty = *ty;
                let next_goal = *body;

                let goal_index = self.goals.len()-1;
                // we place the scaffold of the lambda abstraction
                // and update the current goal
                // we also add a new hole
                let new_hole = self.insert_node(LambdaNode::Hole);
                self.lambda_storage[self.goals[goal_index].node] = LambdaNode::Lam(name.clone(), ty, new_hole);
                self.goals[goal_index].node = new_hole;
                self.goals[goal_index].goal = next_goal;

                // we update the context
                // do note we must update all De Bruijn indices in the context (variables and associated types)
                self
                    .goals[goal_index]
                    .context
                    .push((name, ty));

                Ok(String::from(""))
            },
            _ => Err(Error::EvaluationError(EvaluationError::IntroNotPi)),
        }

    }

    /// method doing the tactic intros on the current goal
    pub fn tact_intros(&mut self, names: Vec<VariableName>) -> Result<String, Error> {
        // the behaviour of intros is fairly different when no names were given
        // we wil intro until we have no more pis
        let full_intro = names.len() == 0;
        if names.len() == 0 { loop {
            // we must intro everything, and this tactic cannot fail anymore
            let goal_index = self
                .goals
                .len()
                .checked_sub(1)
                .ok_or_else(|| InternalError::NoMoreGoalsTactic("intros"))?;
            let goal_node_index = self.goals[goal_index].goal;
            let goal_node = self
                .lambda_storage
                .get(goal_node_index)
                .cloned()
                .ok_or_else(|| InternalError::NodeIncorrectPointer(goal_node_index))?;
            match goal_node {
                LambdaNode::Pi(name, var_ty, body) => {
                    let name = if name.0 == "" {self.get_fresh_hypo_name()} else {name};
                    let new_hole = self.insert_node(LambdaNode::Hole);
                    self.lambda_storage[self.goals[goal_index].node] = LambdaNode::Lam(name.clone(), var_ty, new_hole);
                    self.goals[goal_index].node = new_hole;
                    self.goals[goal_index].goal = body;
                    self.goals[goal_index].context.push((name, var_ty))
                },
                _ => break,
            }
        }} else {
            // we have a defined number of intros, with their names
            // we first check that we can do the right number of intros
            let goal_index = self
                .goals
                .len()
                .checked_sub(1)
                .ok_or_else(|| InternalError::NoMoreGoalsTactic("intros"))?;
            let goal_node_index = self.goals[goal_index].goal;
            let mut goal_node = &self
                .lambda_storage
                .get(goal_node_index)
                .cloned()
                .ok_or_else(|| InternalError::NodeIncorrectPointer(goal_node_index))?;
            for _ in 0..(names.len()) {
                match goal_node {
                    LambdaNode::Pi(_, _, body) => {
                        goal_node = self
                            .lambda_storage
                            .get(*body)
                            .ok_or_else(|| InternalError::NodeIncorrectPointer(*body))?;
                    },
                    _ => return Err(EvaluationError::TooManyIntros.into()),
                }
            }

            // we can now safely do all the intros
            for name in names {
                let goal_index = self
                    .goals
                    .len()
                    .checked_sub(1)
                    .ok_or_else(|| InternalError::NoMoreGoalsTactic("intros"))?;
                let goal_node_index = self.goals[goal_index].goal;
                let goal_node = self
                    .lambda_storage
                    .get(goal_node_index)
                    .cloned()
                    .ok_or_else(|| InternalError::NodeIncorrectPointer(goal_node_index))?;
                match goal_node {
                    LambdaNode::Pi(_, var_ty, body) => {
                        let new_hole = self.insert_node(LambdaNode::Hole);
                        self.lambda_storage[self.goals[goal_index].node] = LambdaNode::Lam(name.clone(), var_ty, new_hole);
                        self.goals[goal_index].node = new_hole;
                        self.goals[goal_index].goal = body;
                        self.goals[goal_index].context.push((name, var_ty));
                    },
                    _ => unreachable!("We just checked that there was the good number of pi"),
                }
            }
        }
        Ok(String::from(""))
    }

    /// does the tactic exact, which is to be given the lambda term representing
    /// exactly the current goal
    /// returns an EvaluationError::ExactMatching if there is some failure
    pub fn tact_exact(&mut self, lamb: LambdaTerm) -> Result<String, Error> {
        let mut ctx = self
            .goals[self.goals.len()-1]
            .context
            .iter().map(|x| x.0.clone())
            .collect();
        let node_index = self.insert_term_ctx(lamb.clone(),&mut ctx)?;
        let typechecking_result = self.typecheck_with_variables_context(
            &mut self.goals[self.goals.len()-1].context.clone(),
            node_index,
            self.goals[self.goals.len()-1].goal.clone(),
        );

        match typechecking_result {
            Ok(()) => {
                self.merge_term(node_index, self.goals[self.goals.len()-1].node);
                self.goals.pop();
                Ok(format!(""))
            }
            Err(e) => {
                let goal_term = self.goals[self.goals.len()-1].goal;
                let mut ctx = self.goals[self.goals.len()-1].context.clone();
                Err(Error::EvaluationError(EvaluationError::ExactMatching(
                lamb,
                self.lambda_to_string_with_context(goal_term, &mut ctx),
                e,
            )))},
        }
    }

    /// the real intro tactic (unused and in the works)
    pub fn tact_true_induction(&mut self, t:VariableName) -> Result<String, Error> {
        let holecontext = &self.goals[self.goals.len()-1];
        let goal_ty = holecontext.goal.clone();
        let goal_lam = holecontext.node.clone();
        let variables = holecontext
            .context
            .iter().map(|x| x.clone())
            .collect::<VariablesContext>();
        let gamma = &holecontext
            .context
            .clone();

        // get type of variable, checking it is an inductive
        let (variable_index,(_,mut tp)) = variables.iter().rev().enumerate().find(|(i,(a,_))|*a == t).ok_or(EvaluationError::UnknowVariableInduction(var_to_string(&t)))?;
        let mut tp_params = vec![];
        let ind = loop {
            match &self.lambda_storage[tp] {
                LambdaNode::Inductive(n) => break n.clone(),
                LambdaNode::App(left,right) => {
                    match  &self.lambda_storage[*right] {
                        LambdaNode::Var(v) => {
                            tp = *left;
                            tp_params.push(v);
                        }
                        _ => return Err(EvaluationError::VariableNotInductive(var_to_string(&t)).into())
                    }
                },
                _ => return Err(EvaluationError::VariableNotInductive(var_to_string(&t)).into())
            };
        };

        // Getting the non-fixed arguments. the last ind_info.parameters.len() are the fixed one
        let ind_info = &self.inductives[&ind.clone()].clone();
        let mut unfixed_params = vec![];
        let l = tp_params.len();
        for (i,x) in tp_params.into_iter().enumerate() {
            if i < l -ind_info.parameters.len() {
                unfixed_params.push(*x);
            } else {break}
        }
        
        let mut unfixed_params = unfixed_params.into_iter().rev().collect::<Vec<DeBruijnIndex>>();

        // get their types, beware of the dependencies!
        let mut unfixed_param_with_types = vec![];
        let mut arity = ind_info.type_of;
        loop {
            match &self.lambda_storage[arity] {
                &LambdaNode::Pi(_,left,right) => {
                    unfixed_param_with_types.push((unfixed_params.pop(),left));
                    arity = right;
                }
                _ => break,
            };
        }

        // build the functional_goal
        let shifted_functional_goal = self.shift_index_keep(1+unfixed_params.len(), 0, goal_ty);

        let function_name = (format!("<invisible>"),0);

        let function_type = self.insert_node(LambdaNode::Pi(t.clone(), tp, shifted_functional_goal));
        let goal_id = self.goals.len()-1;
        self.goals[goal_id].context.push((function_name.clone(),function_type));

        // Creating each branch of the match
        let mut cases = vec![];
        let mut new_goals : Vec<HoleContext> = Vec::new();
        for (i,(cons_name,mut cons_type)) in ind_info.constructors.iter().enumerate() {
            let mut cons_args = vec![];
            loop {
                match self.lambda_storage[cons_type].clone() {
                    LambdaNode::Pi(a_name,a_tp,next) => {cons_args.push((a_name,a_tp));cons_type = next},
                    _ => break,
                }
            }


            // build the pattern
            let pat = cons_args.iter().fold(
                Pattern::Constr(i, ind.clone()),
                |pat,(a,a_tp)|
                Pattern::App(Box::new(pat),Box::new(Pattern::Var((*a).clone())))
            );

            // Like the pattern, build the new variable that `x` will be in this case (same as pattern)
            let mut new_var_in_this_case = self.insert_node(LambdaNode::Constr(i, ind.clone(), tp));
            for (i,(_,_)) in cons_args.iter().enumerate() {
                let var = self.insert_node(LambdaNode::Var(cons_args.len()-i-1));
                new_var_in_this_case = self.insert_node(LambdaNode::App(new_var_in_this_case,var))
            }

            // get new context and the list of argument that are inductive
            let mut rec_hyp = vec![];
            let mut constr_gamma = self.goals[goal_id].context.clone();
            for (i,(arg,arg_tp)) in cons_args.iter().enumerate() {
                if self.lambda_storage[*arg_tp] == LambdaNode::Inductive(ind.clone()) {
                    rec_hyp.push((cons_args.len()-i-1,arg,arg_tp));
                }
                constr_gamma.push(((*arg).clone(),*arg_tp));
            }

            let nb_of_created_vars =cons_args.len()+rec_hyp.len();
            let new_goal_this_case = self.replace_depth_keep(shifted_functional_goal,new_var_in_this_case,variable_index+1);
            let constr_goal = self.shift_index_keep(nb_of_created_vars, 0, new_goal_this_case);
            let mut body = self.insert_node(LambdaNode::Hole);
            let hole_inside = body;
            for (i,arg,arg_tp) in rec_hyp {

                // calculate the type of the induction hypothesis as `P new_var`
                let new_var_in_goal = self.insert_node(LambdaNode::Var(i));
                let hyp_on_arg = self.replace_depth_keep(constr_goal, new_var_in_goal, variable_index+1);

                // add the induction hypothesis
                let var_on_wich_apply_hyp = self.insert_node(LambdaNode::Var(i));
                let recursive_hyp = self.insert_node(LambdaNode::Var(nb_of_created_vars));
                let right = self.insert_node(LambdaNode::App(recursive_hyp,var_on_wich_apply_hyp));
                let left = self.insert_node(LambdaNode::Lam(arg.clone(),*arg_tp,body));
                body = self.insert_node(LambdaNode::App(left, right));
                constr_gamma.push(((*arg).clone(),*arg_tp));
            }

            cases.push((pat,body));

            // create the new hole
            let hole = HoleContext{
                goal:constr_goal,
                node:hole_inside,
                context:constr_gamma,
            };
            new_goals.push(hole);
        };

        // setting up the correct position for the new holes
        self.goals.pop();
        self.goals.append(&mut new_goals);

        let varname_node_inside_fix = self.insert_node(LambdaNode::Var(variable_index+1));
        let match_node = self.insert_node(LambdaNode::Match(
            varname_node_inside_fix, t.clone(), Pattern::Var(t.clone()), goal_ty, cases));
        let fix_node = self.insert_node(LambdaNode::Fix(
            function_name,
            vec![(t.clone(),tp)], 
            t, goal_ty,
            match_node));
        let varname_node_outside_fix = self.insert_node(LambdaNode::Var(variable_index));
        self.lambda_storage[goal_lam] = LambdaNode::App(fix_node,varname_node_outside_fix);
        Ok(format!("Ok"))

    }

    /// helper function tha given a context gamma and a name v, will give an unused VariableName that use the same name 
    pub fn get_new_name(&self, mut v:&str, gamma:&VariablesContext) -> VariableName {
        if v=="" {
            v = "p"
        };
        let n = gamma
            .iter()
            .filter_map(|((str, n), _)| if *str == v {Some(n)} else {None})
            .max();
        let n = match n {
            None => 0,
            Some(n) => n+1
        };
        (v.to_string(), n)
    }

    // For now, only on Inductive without arguments
    pub fn tact_induction(&mut self, t:VariableName) -> Result<String, Error> {
        let holecontext = &self.goals[self.goals.len()-1];
        let goal_ty = holecontext.goal.clone();
        let goal_lam = holecontext.node.clone();
        let variables = holecontext
            .context
            .iter().map(|x| x.clone())
            .collect::<VariablesContext>();
        let gamma = &holecontext
            .context
            .clone();

        let (variable_index,(_,tp)) = variables.iter().rev().enumerate().find(|(i,(a,_))|*a == t).ok_or(EvaluationError::UnknowVariableInduction(var_to_string(&t)))?;
        let ind = match &self.lambda_storage[*tp] {
            LambdaNode::Inductive(n) => n.clone(),
            _ => return Err(EvaluationError::VariableNotInductive(var_to_string(&t)).into())
        };

        // Checking it is a Set inductive type (no depend types for now)
        // todo: add dependant types
        let ind_info = &self.inductives[&ind.clone()].clone();
        if ind_info.parameters.len() != 0 {return Err(EvaluationError::InductiveArity0.into());}
        match self.lambda_storage[ind_info.type_of] {
            LambdaNode::Type(_) => (),
            _ => {return Err(EvaluationError::InductiveArity0.into());}
        }

        // create function type
        let function_name = self.get_new_name("<invisible>",gamma);
        let fix_arg_name = self.get_new_name("fix_arg",gamma);
        let arg_name = self.get_new_name("arg",gamma);
        let mut shifted_functional_goal = self.shift_index_keep(1, 0, goal_ty);
        let v0 = self.insert_node(LambdaNode::Var(0));
        shifted_functional_goal = self.brute_replace_depth_keep(shifted_functional_goal,v0,variable_index); // the goals of fix if on the z as argument not as constant
        let function_type = self.insert_node(LambdaNode::Pi( arg_name.clone(), *tp, shifted_functional_goal));

        // update gamma
        let goal_id = self.goals.len()-1;
        self.goals[goal_id].context.push((fix_arg_name.clone(),*tp));
        self.goals[goal_id].context.push((function_name.clone(),function_type));
        self.goals[goal_id].context.push((arg_name.clone(),*tp)); // add match arg to gamma (no need to shift type as it's Inductive(x))

        // the goal of match is on the last variable created 
        let shifted_functional_goal_for_match = self.shift_index_keep(2, 1, shifted_functional_goal);
        // println!("Return type of match is {}",self.lambda_to_string_with_context(shifted_functional_goal_for_match,&mut self.goals[goal_id].context.clone()));
        
        // Creating each branch of the match
        let mut cases = vec![];
        let mut new_goals : Vec<HoleContext> = Vec::new();
        for (i,(cons_name,mut cons_type)) in ind_info.constructors.iter().enumerate() {
            let mut cons_args = vec![];
            loop {
                match self.lambda_storage[cons_type].clone() {
                    LambdaNode::Pi(a_name,a_tp,next) => {cons_args.push((a_name,a_tp));cons_type = next},
                    _ => break,
                }
            }

            // get new context and the list of argument that are inductive
            let mut rec_hyp = vec![];
            let mut constr_gamma = self.goals[goal_id].context.clone();
            for (i,(arg,arg_tp)) in cons_args.iter().enumerate() {
                let name = self.get_new_name(&arg.0,&constr_gamma);
                if self.lambda_storage[*arg_tp] == LambdaNode::Inductive(ind.clone()) {
                    rec_hyp.push((cons_args.len()-i-1,name.clone(),arg_tp));
                }
                constr_gamma.push((name,*arg_tp));
            }

            // build the pattern
            let pat = cons_args.iter().zip(constr_gamma.iter()).fold(
                Pattern::Constr(i, ind.clone()),
                |pat,((a,a_tp),(name,_))|{
                    Pattern::App(Box::new(pat),Box::new(Pattern::Var(name.clone())))
                }

            );

            let shifted_functional_goal_for_constr = self.shift_index_keep(constr_gamma.len(),1,shifted_functional_goal_for_match);

            // Like the pattern, build the new variable that `x` will be in this case (same as pattern)
            let mut new_var_in_this_case = self.insert_node(LambdaNode::Constr(i, ind.clone(), *tp));
            for (j,(_,_)) in cons_args.iter().enumerate() {
                let var = self.insert_node(LambdaNode::Var(cons_args.len()-j-1));
                new_var_in_this_case = self.insert_node(LambdaNode::App(new_var_in_this_case,var))
            }

            let nb_of_created_vars = cons_args.len()+rec_hyp.len();
            let mut new_goal_this_case = self.brute_replace_depth_keep(shifted_functional_goal_for_constr,new_var_in_this_case,0); // replace x by Cons v1 ... vn
            let mut body = self.insert_node(LambdaNode::Hole);
            let hole_inside = body;
            for (i,arg,arg_tp) in rec_hyp {

                // calculate the type of the induction hypothesis as `P new_var`
                let new_var_in_goal = self.insert_node(LambdaNode::Var(i));
                let hyp_on_arg = self.brute_replace_depth_keep(shifted_functional_goal_for_constr, new_var_in_goal, nb_of_created_vars+1);

                // add the induction hypothesis
                let var_on_wich_apply_hyp = self.insert_node(LambdaNode::Var(i));
                let recursive_hyp = self.insert_node(LambdaNode::Var(cons_args.len()));
                let right = self.insert_node(LambdaNode::App(recursive_hyp,var_on_wich_apply_hyp));
                let ind_name = self.get_new_name("Hind",&constr_gamma);
                let left = self.insert_node(LambdaNode::Lam(ind_name.clone(),hyp_on_arg,body));
                body = self.insert_node(LambdaNode::App(left, right));
                constr_gamma.push(((format!("Hind"),0),hyp_on_arg));
                new_goal_this_case = self.shift_index_keep(1,0,new_goal_this_case);
            }

            cases.push((pat,body));

            // create the new hole
            let hole = HoleContext{
                goal:new_goal_this_case,
                node:hole_inside,
                context:constr_gamma,
            };
            new_goals.push(hole);
        };

        // setting up the correct position for the new holes
        self.goals.pop();
        self.goals.append(&mut new_goals);

        let varname_node_inside_fix = self.insert_node(LambdaNode::Var(variable_index+1));
        let match_node = self.insert_node(LambdaNode::Match(
            varname_node_inside_fix, arg_name, Pattern::Var((format!(""),0)), goal_ty, cases));
        let fix_node = self.insert_node(LambdaNode::Fix(
            function_name,
            vec![(fix_arg_name.clone(),*tp)], 
            fix_arg_name, goal_ty,
            match_node));
        let varname_node_outside_fix = self.insert_node(LambdaNode::Var(variable_index));
        self.lambda_storage[goal_lam] = LambdaNode::App(fix_node,varname_node_outside_fix);
        Ok(format!("Ok"))

    }

    // helper function indicating if ind_name appear in the free variables of t.
    // Used for printing reason to make the difference beetween `forall a:X, B` and `A -> B`
    fn appears_in(&self, t: &LambdaTerm, ind_name: &VariableName) -> bool {
        match t {
            LambdaTerm::Variable(x) => *x == *ind_name,
            LambdaTerm::Application(a, b) => {
                self.appears_in(b, ind_name) || self.appears_in(a, ind_name)
            }
            LambdaTerm::Pi(x, var_ty, body) => {
                self.appears_in(var_ty, ind_name) || (*x != *ind_name && self.appears_in(body, ind_name))
            }
            LambdaTerm::Match(_, _, _, _, _) |
            LambdaTerm::Abstraction(_, _, _) |
            LambdaTerm::Let(_, _, _, _) |
            LambdaTerm::Constr(_, _, _) |
            LambdaTerm::Fix(_, _, _, _, _) => true, /* If I don't know what's going on, worst case scenario */
            LambdaTerm::Set |
            LambdaTerm::Prop |
            LambdaTerm::Type(_) => false
        }
    }

    // ----- Functions used to test an inductive type is well formed -----

    // given a lambda term of the form `<var> A1 ... AN`, will return `<var>`
    fn get_head<'a>(&self, mut t: &'a LambdaTerm) -> Result<&'a VariableName, ()> {
        while let LambdaTerm::Application(a, _) = t {
            t = a;
        }
        if let LambdaTerm::Variable(x) = t {
            Ok(x)
        } else {
            Err(())
        }
    }

    fn strict_positive_only(&self, t: &LambdaTerm, ind_name: &VariableName, params: &Vec<VariableName>, arity_length: usize) -> bool {
        let mut temp = t;
        if !self.appears_in(temp, ind_name) {
            return true
        }
        while let LambdaTerm::Pi(x, a, b) = t {
            if self.appears_in(a, ind_name) {return false} else if *x == *ind_name {return true} else {
                temp = b;
            }
        }
        if self.is_actually_being_defined_inductive(temp, ind_name, params, arity_length).is_ok() {
            return true
        }
        let ind = match self.get_head(temp) {
            Ok(x) => x,
            _ => return false
        };
        if !self.inductives.contains_key(ind) {
            return false
        } else {
            let ind_data = &self.inductives[ind];
            // todo: this part
        }
        false
    }

    fn is_actually_being_defined_inductive(&self, mut cons: &LambdaTerm, ind_name: &VariableName, params: &Vec<VariableName>, mut arity_length: usize) -> Result<(), Error> {
        use LambdaTerm::*;
        let mut params = params.clone();
        while arity_length > 0 {
            match cons {
                Application(a, b)
                    if !self.appears_in(b, ind_name) => {cons = a; arity_length -= 1;}
                Application(..) | Variable(_) | Abstraction(..) |
                Pi(..) | Let(..) | Set | Prop | Type(_) |
                Constr(..) | Fix(..) | Match(..) => return Err(Error::EvaluationError(EvaluationError::InvalidArity))
            }
        }
        while let Some(t) = params.pop() {
            match cons {
                Application(x, y) if
                    if let Variable(tx) = &**y {*tx == t} else {false} =>
                    {
                        cons = x
                    }
                Variable(_) | Abstraction(..) | Application(..) |
                Pi(..) | Let(..) | Set | Prop | Type(_) |
                Constr(..) | Match(..) | Fix(..) => return Err(Error::EvaluationError(EvaluationError::InvalidArity))
            }
        }
        match cons {
            Variable(x) if *x == *ind_name => Ok(()),
            Variable(_) | Abstraction(..) | Application(..) |
            Pi(..) |Let(..) |Set | Prop | Type(_) |
            Constr(..) | Match(..) | Fix(..) => Err(Error::EvaluationError(EvaluationError::InvalidArity))
        }
    }

    fn constructor_type_is_valid(&mut self, mut cons: &LambdaTerm, ind_name: &VariableName, params: &Vec<VariableName>, arity_length: usize) -> Result<(), Error> {
        use LambdaTerm::*;
        while let LambdaTerm::Pi(x, var_ty, cons0) = cons {
            if x == ind_name {
                return Err(Error::EvaluationError(EvaluationError::InvalidArity))
            } else if self.strict_positive_only(var_ty, ind_name, params, arity_length) {
                cons = cons0
            } else {
                return Err(Error::EvaluationError(EvaluationError::InvalidArity))
            }
        }
        match cons {
            Application(..) | Variable(_) =>
                self.is_actually_being_defined_inductive(cons, ind_name, params, arity_length),
            Pi(..) | Abstraction(..) | Let(..) | Prop | Type(_) |
            Set | Constr(..) | Match(..) | Fix(..) =>
                Err(Error::EvaluationError(EvaluationError::InvalidArity)),
        }
    }

    fn predicative_prop(&mut self, mut t: NodeIndex, mut params_length: usize) -> Eliminability {
        // we retrieve the parameters, they will be used as a typing context
        let mut context = Vec::new();
        while params_length > 0 {
            if let LambdaNode::Pi(ref var_name, var_ty, b) = self.lambda_storage[t] {
                t = b;
                context.push((var_name.clone(), var_ty));
                params_length -= 1;
            } else {
                panic!("Erreur")
            }
        }
        let prop = self.insert_node(LambdaNode::Prop);
        while let LambdaNode::Pi(v, a, b) = self.lambda_storage[t].clone() {
            let type_x = self.get_type(&mut context, a).unwrap();
            if !self.subtype(&mut context, type_x, &mut Vec::new(), prop).is_ok() {
                return Eliminability::Uneliminable
            } /* Else it's Prop and it's still eliminable */
            t = b;
            context.push(((v.clone()),a));
        }
        Eliminability::Eliminable
    }

    // Check that an inductive definition is valid and then insert it in the global context
    pub fn add_inductive(&mut self, name:VariableName, params:Vec<InductiveParams>, arity:LambdaTerm, constructors:Vec<InductiveConstrDef>) -> Result<String, Error> {
        //Checking that the inductive definition is valid

        // For now we skip the checks and assume that the definition is well formed
        //eprintln!("For now there is no checks that the inductive defintion is valid.");
        //Step 1: checking that the arity is valid (i.e. Pi (y1: B1)..(yp: Bp) s where s is a sort (Type, Prop, Set))
        let mut arity_length: usize = 0;
        let s = {
            let mut actual = arity.clone();
            while let LambdaTerm::Pi(_, _, next) = actual{
                actual = *next;
                arity_length += 1;
            }
            match actual {
                LambdaTerm::Set => LambdaTerm::Set,
                LambdaTerm::Prop => LambdaTerm::Prop,
                LambdaTerm::Type(n) => LambdaTerm::Type(n),
                _ => return Err(Error::EvaluationError(EvaluationError::InvalidArity)),
            }
        };

        //Step 2: We need to check that the constructors are well-typed

        // all constructorrs can depend on the parameters so we build the appropriate context
        let mut ctx : Vec<_> = params.iter().map(|(name, _)| name.clone()).collect();

        let i_type = {
            let mut actual = arity;
            for (name, t) in params.iter().rev(){
                actual = LambdaTerm::Pi(name.clone(), Box::new(t.clone()), Box::new(actual));
            }
            actual
        };

        let i_type_node = self.insert_term_ctx(i_type.clone(), &mut ctx)?; // hope we can just send back the error, if not, oups, sorry
        let i_type_type = match self.get_type(&mut Vec::new(), i_type_node) {
            Ok(x) => x,
            Err(x) => return Err(Error::EvaluationError(EvaluationError::TypingError(x)))
        };
        match self.lambda_storage[i_type_type] {
            LambdaNode::Prop | LambdaNode::Type(_) => (),
            _ => return Err(Error::EvaluationError(EvaluationError::InvalidArity))
        }

        let expected_type = {
            let mut actual = s.clone();
            for (name, t) in params.iter().rev(){
                actual = LambdaTerm::Pi(name.clone(), Box::new(t.clone()), Box::new(actual));
            }
            LambdaTerm::Pi(name.clone(), Box::new(i_type.clone()), Box::new(actual))
        };
        let expected_type_node = self.insert_term(expected_type)?;

        // Check type of each constructor 
        for (_, c) in &constructors {
            let to_typecheck = {
                let mut actual = c.clone();
                for (name, t) in params.iter().rev(){
                    actual = LambdaTerm::Abstraction(name.clone(), Box::new(t.clone()), Box::new(actual));
                }
                LambdaTerm::Abstraction(name.clone(), Box::new(i_type.clone()), Box::new(actual))
            };
            let lambda = self.insert_term(to_typecheck)?;

            if let Err(e) = self.typecheck_with_variables_context(&mut Vec::new(), lambda, expected_type_node){
                return Err(Error::EvaluationError(EvaluationError::TypingError(e)));
            }
        }

        // Check condition on each constructor 
        for (_, c) in &constructors {
            self.constructor_type_is_valid(c, &name, &params.iter().map(|x| x.0.clone()).collect::<Vec<_>>(), arity_length)?
        }

        self.inductives.insert(name.clone(), Default::default());

        let mut constructors_list = Vec::new();

        for (n, (constr_name, body)) in constructors.into_iter().enumerate(){
            let constructor_type = {
                let mut actual = body;
                for (pars_name, pars_type) in params.iter().rev(){
                    actual = LambdaTerm::Pi(pars_name.clone(), Box::new(pars_type.clone()), Box::new(actual));
                }
                actual
            };
            constructors_list.push((constr_name.clone(), self.insert_term(constructor_type)?));
        }

        let mut parameters = Vec::new();
        let mut ctx = Vec::new();
        for (name, t) in &params {
            let t = self.insert_term_ctx(t.clone(), &mut ctx)?;
            parameters.push((name.clone(), t));
            ctx.push(name.clone())
        }

        // todo: cleanup
        let elim = match s {
            LambdaTerm::Prop => {
                if constructors_list.len() == 0 {
                    Eliminability::Eliminable
                }
                else if constructors_list.len() == 1 {
                    let (_, t) = &constructors_list[0];
                    self.predicative_prop(*t, params.len())
                } else {
                    Eliminability::Uneliminable
                }
            }
            _ => Eliminability::Eliminable,
        };

        let ind_data = InductiveData::new(
            parameters,
            i_type_node,
            constructors_list,
            elim
        );
        self.inductives.insert(name.clone(), ind_data);
        Ok(format!("`{}` is defined inductively", var_to_string(&name)))
    }

    /// (force)Reset the current proof context to a proof of l.
    /// Consider using `self.clean()` defined in `manager.rs` after this call.
    pub fn set_goal_overwrite(&mut self, l:LambdaTerm, name:Option<VariableName>) -> Result<String,Error> {
        let to_prove = self.insert_term(l)?;
        let pos = self.insert_node(LambdaNode::Hole);
        self.goals = vec![HoleContext::new(to_prove, pos)];
        let root = ProofInfo::new(name,to_prove,pos);
        self.root = Some(root);
        return Ok(format!(""));
    }

    /// Start a proof of l *if no proof are already in progress*.
    pub fn set_goal(&mut self, l:LambdaTerm) -> Result<String,Error> {
        if let Some(_) = self.root {
            return Err(Error::EvaluationError(EvaluationError::AlreadyProof))
        }
        self.set_goal_overwrite(l,None)
    }

    /// Start a proof of l *if no proof are already in progress*, and upon completion
    /// will store in in the constants.
    pub fn set_goal_named(&mut self, l:LambdaTerm, name:VariableName) -> Result<String,Error> {
        if let Some(_) = self.root {
            return Err(Error::EvaluationError(EvaluationError::AlreadyProof))
        }
        self.set_goal_overwrite(l,Some(name))
    }

    /// Implement the Definition command
    pub fn define(&mut self, name:VariableName, lamb:LambdaTerm) -> Result<(),Error> {
        if let Some((_,x)) = self.constants.get(&name) {
            return Err(EvaluationError::TheoremAlreadyExists(var_to_string(&name),self.lambda_to_string(*x)).into())
        }
        let node_id = self.insert_term(lamb)?;
        let tp = self.get_type(&mut vec![], node_id).map_err(|x| Error::EvaluationError(EvaluationError::DefineNotTypable(var_to_string(&name),x).into()))?;
        self.constants.insert(name,(node_id,tp));
        Ok(())
    }

    /// Close the current proof if possible and add the object/proof into the constants.
    pub fn qed(&mut self) -> Result<String, Error> {
        let proof_info = match &self.root {
            None => return Err(Error::EvaluationError(EvaluationError::NoProof)),
            Some(pi) => pi,
        };
        if self.goals.len() > 0 {
            return Err(Error::EvaluationError(EvaluationError::UnfinishedGoals))
        };

        let root = proof_info.root;
        let prop = proof_info.prop;
        let name_opt = proof_info.name.clone();
        // println!("{}", self.lambda_to_string(root));
        match self.typecheck_with_variables_context(&mut vec![], root , prop) {
            Ok(()) => {
                let otp = if let Some(name) = name_opt {
                    self.constants.insert(name.clone(),(root,prop));
                    Ok(format!("Proof of {} completed.",var_to_string(&name)))
                } else {
                    Ok(format!("Proof completed."))
                };
                self.root = None;
                otp
            },
            Err(x) => Err(Error::InternalError(InternalError::QedFailed(self.lambda_to_string(prop),x)))
        }
    }

    /// Abandon the current proof, and clean the state
    pub fn reset(&mut self) -> Result<(), InternalError> {
        self.goals.clear();
        self.root = None;
        // constants stay the same !
        self.clean().map(|x| ())
    }

    // traverse the lambda node recursivly to mark which terms are used
    fn lambda_traversal_mark(
        &self,
        node: NodeIndex,
        set: &mut HashSet<NodeIndex>,
    ) -> Result<(), InternalError> {
        set.insert(node);
        use LambdaNode::*;
        match match self.lambda_storage.get(node) {
            None => return Err(InternalError::NodeIncorrectPointer(node)),
            Some(e) => e,
        } {
            Var(_) | Const(_) | Inductive(_) | Prop | Type(_) | Hole => (),
            App(a, b) => {
                self.lambda_traversal_mark(*a, set)?;
                self.lambda_traversal_mark(*b, set)?
            }
            Let(_, a, b, c) => {
                self.lambda_traversal_mark(*a, set)?;
                self.lambda_traversal_mark(*b, set)?;
                self.lambda_traversal_mark(*c, set)?
            }
            Lam(_, a, b) => {
                self.lambda_traversal_mark(*a, set)?;
                self.lambda_traversal_mark(*b, set)?
            }
            Pi(_, a, b) => {
                self.lambda_traversal_mark(*a, set)?;
                self.lambda_traversal_mark(*b, set)?
            }
            Constr(_, _, t) => {
                self.lambda_traversal_mark(*t, set)?
            },
            Match(t, x, _, r, v) => {
                self.lambda_traversal_mark(*t, set)?;
                self.lambda_traversal_mark(*r, set)?;
                for (_, ei) in v {
                    self.lambda_traversal_mark(*ei, set)?
                }
            }
            Fix(_, args, _, tp, lamb) => {
                self.lambda_traversal_mark(*tp, set)?;
                self.lambda_traversal_mark(*lamb, set)?;
                for (_, ei) in args {
                    self.lambda_traversal_mark(*ei, set)?
                }
            }
        };
        Ok(())
    }

    /// Clean the state and removes unused lambda terms. Return the number of freed elements.
    pub fn clean(&mut self) -> Result<usize, InternalError> {
        use crate::manager::LambdaNode::*;
        let mut used = HashSet::new();
        // mark used lambda term in the goals and constants
        for x in self.goals.iter() {
            self.lambda_traversal_mark(x.goal, &mut used)?;
        }
        for (_, (a, b)) in self.constants.iter() {
            self.lambda_traversal_mark(*a, &mut used)?;
            self.lambda_traversal_mark(*b, &mut used)?;
        }
        if used.len() == self.lambda_storage.len() {
            return Ok(0);
        }
        let length = self.lambda_storage.len();
        // create a "rescaling map" that to a nodeIndex give the new NodeIndex
        let mut values = HashMap::new();
        for (i, v) in used.iter().enumerate() {
            values.insert(v.clone(), i.clone());
        }
        // rescale a node to use the new indices
        let fixed = |m| match m {
            Var(_) | Const(_) | Inductive(_) | Prop | Type(_) | Hole => m,
            App(a, b) => App(*values.get(&a).unwrap(), *values.get(&b).unwrap()),
            Let(var_name, a, b, c) => Let(
                var_name,
                *values.get(&a).unwrap(),
                *values.get(&b).unwrap(),
                *values.get(&c).unwrap(),
            ),
            Lam(name, a, b) => Lam(name, *values.get(&a).unwrap(), *values.get(&b).unwrap()),
            Pi(name, a, b) => Pi(name, *values.get(&a).unwrap(), *values.get(&b).unwrap()),
            Constr(n, i, t) => Constr(n, i, *values.get(&t).unwrap()),
            Match(t, x, p, r, v) => Match(
                *values.get(&t).unwrap(),
                x,
                p,
                *values.get(&r).unwrap(),
                v.into_iter().map(|(pi, ei)| (pi, *values.get(&ei).unwrap())).collect(),
            ),
            Fix(name,args,stru,tp,expr) => Fix(
                name,
                args.into_iter().map(|(n,e)|(n,*values.get(&e).unwrap())).collect(),
                stru,
                *values.get(&tp).unwrap(),
                *values.get(&expr).unwrap(),
            ) 
        };
        // filter then apply to all of the lambda_storage
        self.lambda_storage = self
            .lambda_storage
            .to_owned()
            .into_iter()
            .enumerate()
            .filter(|(i, _)| used.contains(i))
            .map(|(i, x)| fixed(x))
            .collect();
        Ok(length - self.lambda_storage.len())
    }

    /// Switches goal 1 for goal `goalId`
    pub fn switch_goal(self, goal_id: usize) -> Result<(), ()> {
        todo!()
    }

    /// Add (load) a theorem / definition to the list of available theorem. Used to dynamically add a theorem / property. TODO
    pub fn add_theorem(self, lt: LambdaTerm, name: VariableName) {
        todo!()
    }

    /// Get the list of hypothesis of the curent active goal.
    /// Used for printing / debbugging purpose
    pub fn get_hypothesis(&self) -> Vec<String> {
        match &self.root {
            None => Vec::new(),
            Some(_) if self.goals.len() == 0 => Vec::new(),
            Some(_) => {
                let hole_context = &self.goals[self.goals.len()-1];
                let context = &mut hole_context.context.clone();

                // we will have to pop a variable after having seen it
                // we will store them in unwind, then push them again
                let mut unwind = Vec::new();
                let mut hypothesis = Vec::new();
                for (name, ty) in hole_context.context.iter().rev() {
                    // we pop the variable we have juste seen, as the type will have
                    // to be interpreted in a context where it is not present
                    unwind.push(context.pop().unwrap());
                    let name = var_to_string(name);
                    let ty = self.lambda_to_string_with_context(*ty, context);
                    hypothesis.push(format!("{} : {}", name, ty));
                }
                // we do NOT forget to get back the context
                context.extend(unwind.into_iter().rev());
                hypothesis.into_iter().rev().collect::<Vec<String>>()

            }
        }
    }

    /// Get a french variable name unused in the current goal.
    pub fn get_fresh_hypo_name(&self) -> VariableName {
        let goal = &self.goals[self.goals.len()-1];
        let n = goal
            .context
            .iter()
            .filter_map(|((str, n), _)| if *str == String::from("H") {Some(n)} else {None})
            .max();
        let n = match n {
            None => 0,
            Some(n) => n+1
        };
        (String::from("H"), n)
    }

    // Execute a single command as a &str, and return either the output message or an Error by calling `self.command`
    pub fn exec_command(&mut self, text:&str) -> Result<String,Error> {
        let parsed = parsing::parse_command(text);
        match parsed {
            Err(e) => Err(Error::Parsing(format!("{e}"))),
            Ok(command) => self.command(command),
        }
    }

    // Execute multiple commands as a &str, and return either the error of the first command or the output (as a String) of the last one, by calling `self.commands`
    pub fn exec_commands(&mut self, text:&str) -> Result<String,Error> {
        let parsed = parsing::parse_commands(text);
        match parsed {
            Err(e) => Err(Error::Parsing(format!("{e}"))),
            Ok(command) => self.commands(command),
        }
    }
}

#[cfg(test)]
mod tests {

    #[allow(unused)]
    use crate::definitions::*;
    #[allow(unused)]
    use crate::*;

    #[test]
    pub fn prop_to_prop() {
        let mut proof = GlobalContext::new();
        assert!(proof.exec_commands("Goal Prop -> Prop. exact (fun (x:Prop) => x). Qed.").is_ok());
        assert_eq!(proof.root, None);
    }

    #[test]
    pub fn simple_forall() {
        let mut proof = GlobalContext::new();
        assert!(proof.exec_commands("Goal forall A:Prop, A -> A. exact fun (A:Prop) => fun (x:A) => x. Qed.").is_ok());
        assert_eq!(proof.root, None);
    }

    #[test]
    pub fn intro1() {
        let mut proof = GlobalContext::new();
        assert!(proof.exec_commands("Goal forall A:Prop, A -> A. exact fun (A:Prop) => fun (x:A) => x. Qed.").is_ok());
        assert_eq!(proof.root, None);
    }

    #[test]
    pub fn intro2() {
        let mut proof = GlobalContext::new();
        assert!(proof.exec_commands("Goal Prop -> Prop. intro A. exact A. Qed.").is_ok());
        assert_eq!(proof.root, None);
    }

    #[test]
    pub fn prop_simple_intro() {
        let mut proof = GlobalContext::new();
        assert!(proof.exec_commands("Goal forall A:Prop, A -> A. intro A. intro h. exact h. Qed.").is_ok());
        assert_eq!(proof.root, None);
    }

    #[test]
    pub fn simple_intros() {
        let mut proof = GlobalContext::new();
        let temp = proof.exec_commands("Goal forall A:Prop, forall B:Prop, (A->B)->A->B. intros A B f x. exact f x. Qed.");
        assert!(temp.is_ok());
        assert_eq!(proof.root, None);
    }


    #[test]
    pub fn bot_one() {
        let mut proof = GlobalContext::new();
        let temp =
        proof.exec_commands("Goal forall A:Prop, forall B:Prop, (forall C:Prop, C) -> (A -> B) -> B. intros A B bot f. exact f (bot A). Qed.");
        assert!(temp.is_ok());
        assert_eq!(proof.root, None);
    }

    #[test]
    pub fn bot_two() {
        let mut proof = GlobalContext::new();
        let temp =
        proof.exec_commands("Goal forall A:Prop, forall B:Prop, (forall C:Prop, C) -> A -> B. intros A B bot. exact (bot (A -> B)). Qed.");
        assert!(temp.is_ok());
        assert_eq!(proof.root, None);
    }

    #[test]
    pub fn false_refl() {
        let mut proof = GlobalContext::new();
        let temp = proof.exec_commands("Goal (forall P:Prop, P) -> (forall Q:Prop, Q). intros f. exact f. Qed.");
        assert!(temp.is_ok());
        assert_eq!(proof.root, None);
    }

    #[test]
    pub fn theorem_one() {
        let mut proof = GlobalContext::new();
        assert!(proof.exec_commands("Theorem uwu : forall A:Prop, A -> A. exact fun (A:Prop) => fun (x:A) => x. Qed. Goal forall B:Prop, B -> B. exact uwu. Qed.").is_ok());
        assert_eq!(proof.root, None);
    }

    #[test]
    pub fn bot(){
        let mut proof = GlobalContext::new();
        assert!(
            proof.exec_commands("
                Definition bot := forall X:Prop, X.
                Goal forall A:Prop, bot -> A.
                unfold bot. intros A h. exact h A.
                Qed.
            ").is_ok());
        assert_eq!(proof.root, None);
    }

    #[test]
    pub fn not(){
        let mut proof = GlobalContext::new();
        assert!(
            proof.exec_commands("
                Definition bot := forall X:Prop, X.
                Definition not := fun (A:Prop) => A -> bot.
                Goal forall A:Prop, A -> not A -> bot.
                unfold not. unfold bot. simpl.
                intros B b nb x.
                exact nb b x.
                Qed.
            ").is_ok());
        assert_eq!(proof.root, None);
    }

    #[test]
    pub fn apply_as_exact(){
        let mut proof = GlobalContext::new();
        assert!(
            proof.exec_commands("
                Goal forall A:Prop, A -> A. intros B h. apply h. Qed.
            ").is_ok());
        assert_eq!(proof.root, None);
    }

    #[test]
    pub fn apply_two(){
        let mut proof = GlobalContext::new();
        assert!(
            proof.exec_commands("
                Goal forall A:Prop, forall B:Prop, (A -> B) -> A -> B. intros A B h x. apply h. exact x. Qed.
            ").is_ok());
        assert_eq!(proof.root, None);
    }

    #[test]
    pub fn apply_bigger(){
        let mut proof = GlobalContext::new();
        assert!(
            proof.exec_commands("
                Goal forall A:Prop, forall B:Prop, (A -> B -> A) -> A -> B -> A. intros A B h x. apply h. exact x. Qed.
            ").is_ok());
        assert_eq!(proof.root, None);
    }

    #[test]
    pub fn apply_multiple(){
        let mut proof = GlobalContext::new();
        assert!(
            proof.exec_commands("
                Goal forall A:Prop, forall B:Prop, forall C:Prop, forall D:Prop, forall E:Prop, (A -> B -> C -> D -> E) -> A -> B -> C -> D -> E.
                intros A B C D E h a b c d. apply h. exact a. exact b. exact c. exact d. Qed.
            ").is_ok());
        assert_eq!(proof.root, None);
    }


    #[test]
    pub fn succ(){
        let mut proof = GlobalContext::new();
        assert!(
            proof.exec_commands("
                Definition X := Prop.
                Definition F := X -> X.
                Definition int := F -> F.
                Definition succ := fun (n:int) => fun (f:F) => fun (x:X) => f ((n f) x).
                Definition succsucc := fun (n:int) => fun (f:F) => fun (x:X) => f (f ((n f) x)).
            ").is_ok());
        assert_eq!(proof.root, None);
    }

    #[test]
    pub fn exists() {
        let mut proof = GlobalContext::new();
        assert!(
            proof.exec_commands("
                Definition exists := fun (A: Type(12)) => fun (P: A -> Prop) => forall P0: Prop,
                (forall x: A, P x -> P0) -> P0.

                Definition exintro := fun (A: Type(12)) => fun (P: A -> Prop) => fun (x: A) =>
                fun (H: P x) => fun (P0: Prop) => fun (H0: forall x: A, P x -> P0) => H0 x H.

                Definition True := forall A: Prop, A -> A.

                Definition I := fun (A: Prop) => fun (x: A) => x. 

                Check True.

                Check exintro Type(1) (fun (x:Type(1)) => True).

                Goal exists Type(1) (fun (x:Type(1)) => True).
                unfold exists. simpl. simpl.
                exact fun (P0: Prop) => fun (H: Type(1) -> True -> P0) => H Prop I.
                Qed.
            ").is_ok());
        assert_eq!(proof.root, None);
    }

    #[test]
    pub fn ensure_beta_reduction() {
        let mut proof = GlobalContext::new();
        assert!(
            proof.exec_commands("
                Definition eq := 
                fun (A: Type(12)) => fun (x: A) => fun (y: A) => forall P: A -> Prop, P x -> P y.

                Goal eq Type(1) Prop Prop.
                exact fun (P: Type(1) -> Prop) => fun (H: P Prop) => H.
                Qed.
            ").is_ok());
        assert_eq!(proof.root, None);
    }

    #[test]
    pub fn basic_match_typecheck() {
        let mut proof = GlobalContext::new();
        let _ = proof.exec_commands("
        Inductive test : Prop := cons : test.
        Check match cons as x in test return test with | cons => cons end.
        ");
    }

    #[test]
    pub fn exfalso() {
        let mut proof = GlobalContext::new();
        let _ = proof.exec_commands("
            Inductive False : Prop := .
            Goal forall P:Prop, False -> P.
            intros P bot.
            exact match bot as x in False return P with end.
            Qed.
        ");
        assert_eq!(proof.root, None);
    }

    #[test]
    pub fn ind_false_tests() {
        let mut proof = GlobalContext::new();
        let _ = proof.exec_commands("
            Inductive False : Prop := .

            Goal forall P:Prop, False -> P.
            intros P bot.
            exact match bot as x in False return P with end.
            Qed.

            Def not (P:Prop) := P -> False.

            Goal forall A:Prop, A -> (not (not A)).
            intros. unfold not. simpl. intros. apply H1. exact H.
            Qed.

            Def exfalso (P:Prop) (bot:False) := match bot as _ in False return P with end.

            Goal forall (A B : Prop), A -> not A -> B.
            intros. simpl. unfold not. exact (exfalso B (H1 H)).
            Qed.
        ");
        assert_eq!(proof.root, None);
    }

    #[test]
    pub fn box_type() {
        let mut proof = GlobalContext::new();
        let _ = proof.exec_commands("
            Inductive box (A:Prop) : Prop := b : A -> box A.

            Goal forall (A:Prop), box A -> A.
            intros A bo.
            exact match bo as _ in box _ return A with | b _ x => x end.
            Qed.

            Goal forall (A B:Prop), (box A -> B) -> A -> B.
            intros. apply H. exact b A H1. Qed.

            Goal forall (A B:Prop), (A -> B) -> box A -> B.
            intros A B H H1. apply H.
            exact match H1 as _ in box _ return A with | b _ x => x end.
            Qed.
        ");
        assert_eq!(proof.root, None);
    }

    #[test]
    pub fn and() {
        let mut proof = GlobalContext::new();
        let _ = proof.exec_commands("
            Inductive and (A B:Prop) : Prop := conj : A -> B -> and A B.

            Goal forall (A B C:Prop), and A B -> C -> and B C.
            intros A B C H z.
            exact match H as _ in and _ _ return and B C with | conj _ _ _ y => conj B C y z end.
            Qed.

            Goal forall (A B:Prop), and A B -> A.
            intros A B H.
            exact match H as _ in and _ _ return A with | conj _ _ x _ => x end.
            Qed.

            Goal forall (A B:Prop), A -> B -> and A B.
            intros A B x y.
            exact conj A B x y.
            Qed.

            Goal forall (A B:Prop), and A B -> and B A.
            intros A B H.
            exact match H as _ in and _ _ return and B A with | conj _ _ x y => conj B A y x end.
            Qed.
        ");
        assert_eq!(proof.root, None);
    }

    #[test]
    pub fn or() {
        let mut proof = GlobalContext::new();
        let _ = proof.exec_commands("
            Inductive or (A B:Prop) : Prop :=
            | inj1 : A -> or A B
            | inj2 : B -> or A B.

            Goal forall A:Prop, A -> or A A.
            intros A x. exact inj1 A A x. Qed.

            Goal forall (A B C:Prop), (A -> C) -> (B -> C) -> or A B -> C.
            intros A B C f g o.
            exact match o as _ in or _ _ return C with
            | inj1 _ _ x => f x
            | inj2 _ _ x => g x
            end.
            Qed.
        ");
        assert_eq!(proof.root, None);
    }

    #[test]
    pub fn eq() {
        let mut proof = GlobalContext::new();
        let _ = proof.exec_commands("
            Inductive eq (A:Type(42)) (x:A) : A -> Prop := eq_refl : eq A x x.

            Goal forall (A:Prop) (x y: A), eq A x y -> eq A y x.
            intros A x y H.
            exact match H as _ in eq _ _ t return eq A t x with | eq_refl _ _ => eq_refl A x end.
            Qed.

            Inductive eq (A:Type(42)) (x:A) : A -> Prop := eq_refl : eq A x x.

            Goal forall (A B:Type(42)) (f:A->B) (x y : A), eq A x y -> eq B (f x) (f y).
            intros A B f x y H.
            exact match H as _ in eq _ _ t return eq B (f x) (f t) with
            | eq_refl _ _ => eq_refl B (f x) end.
            Qed.

        ");
        assert_eq!(proof.root, None);
    }

    #[test]
    pub fn list() {
        let mut proof = GlobalContext::new();
        let _ = proof.exec_commands("
Inductive list (A: Set) : Set :=
  | nil : list A
  | cons : A -> list A -> list A.

Fixpoint concat (A: Set) (l1: list A) (l2: list A) {struct l1} : list A :=
  match l1 as _ in list _ return list A with
    | nil _ => l2
    | cons _ x q => cons A x (concat A q l2)
  end.
        ");
    }

    #[test]
    pub fn oskur() {
        let mut proof = GlobalContext::new();
        let temp = proof.exec_commands("
        Inductive nat : Set := 0 : nat | S : nat -> nat.

        
        Inductive list : Set :=
  | nil : list
  | cons : nat -> list -> list.

Fixpoint list_ind (l: list) (P: list -> Prop) (H0: P nil) 
  (Hcons: forall (x: nat) (l: list), P l -> P (cons x l))
  {struct l} : P l := 
  match l as x in list return P x with 
    | nil => H0
    | cons x q => Hcons x q (list_ind q P H0 Hcons)
  end.
        
        ");
        println!("{temp:?}");
    }


}