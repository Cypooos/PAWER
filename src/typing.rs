use crate::definitions::{var_to_string, TypingContext, Eliminability, GlobalContext, LambdaNode, NodeIndex, Pattern, VariableName, VariablesContext};
use crate::errors::{TypingError};
use TypingError::*;
use std::cmp::max;
use std::iter::zip;
use std::usize;
// This file contain all typing-related functions

macro_rules! get_node {
    ($self:tt, $index:tt) => {
        $self.lambda_storage
            .get($index)
            .cloned()
            .ok_or_else(|| TypingError::NodeIncorrectPointer($index))?
    };
}

#[allow(dead_code, unused_variables)]
impl GlobalContext {

    // Once we have `get_type` and `subtype`, `typecheck(e,t)` can then be defined as a subtype(get_type(e),t) (what we did)
    /// Checks if `lambda` can be given the type `target_type`
    /// The context is a `VariablesContext`, i.e. the stack of named variables
    /// with their Deb Bruijn indices and node indices
    /// the functions handles building a proper `Context`, making
    /// the suited temporary modifications to the storage, and rolling them back afterwards
    pub fn typecheck_with_variables_context(
        self: &mut Self,
        gamma: &mut VariablesContext,
        lambda: NodeIndex,
        target_type: NodeIndex
    ) -> Result<(), TypingError> {
        let mut temp = gamma.clone();
        let ty = self.get_type(&mut temp, lambda)?;
        // we unfold constants and beta reduce before checking the subtyping
        let ty = self.unfold_constants(ty).unwrap();
        let target_type = self.unfold_constants(target_type).unwrap();
        self.beta_reduction(ty);
        self.beta_reduction(target_type);
        self.subtype(&mut temp, ty, gamma, target_type)
    }

    /// Gets the minimal type for ``lam`` in the context ``gamma``.
    /// It returns the ``NodeIndex`` of said type in ``self.lambda_storage``.
    /// If the lambda term corresponding to the type was not already stored,
    /// all the necessary allocations will be made.
    /// do note that altough gamma will be modified, it will be returned as
    /// it was provided, even if an error occurs
    pub fn get_type(
        &mut self,
        gamma: &mut TypingContext,
        lam: NodeIndex,
    ) -> Result<NodeIndex, TypingError> {
        use LambdaNode::*;
        match get_node!(self, lam) {
            Var(i) => {
                let var_index = gamma.len() - i - 1;
                let var_ty_index = gamma
                    .get(var_index)
                    .map(|(_, ind)| *ind)
                    .ok_or_else(||UnboundVariable(i))?;
                let otp = self.deep_copy(var_ty_index);
                self.shift_index_overwrite(1+i as isize, otp);
                Ok(otp)
            }
            Const(c) => {
                self.constants
                    .get(&c)
                    .map(|(_, ty)| *ty)
                    .ok_or_else(|| UndefinedConstant(var_to_string(&c)))
            },
            Pi(var_name, var_t, bod_t) => {
                gamma.push((var_name.clone(), var_t));
                let bod_t = self.get_type(gamma, bod_t);
                gamma.pop();
                let bod_t = bod_t?;

                // if the body is prop, there is no need to look at the type of the variable's type
                // if it is some Type, then we need to ensure that the body and the type of the var type
                // live in the same universe
                match get_node!(self, bod_t) {
                    Prop => Ok(self.insert_node(Prop)),
                    Type(i) => {
                        let var_type_type = self.get_type(gamma, var_t)?;
                        match get_node!(self, var_type_type) {
                            Type(j) => Ok(self.insert_node(Type(max(i, j)))),
                            Prop => Ok(self.insert_node(Type(max(i, 1)))),
                            _ => {
                                let var_type_type_str = self.lambda_to_string_with_context(var_type_type, gamma);
                                let msg = format!("Pi-type variable's type is not a sort but {var_type_type_str}");
                                Err(TypeIncoherence(msg))
                            }
                        }
                    }
                    _ => {
                        gamma.push((var_name, var_t));
                        let bod_ty_str = self.lambda_to_string_with_context(bod_t, gamma);
                        gamma.pop();
                        let msg = format!("invalid type for a Pi-type body: {bod_ty_str}");
                        Err(TypeIncoherence(msg))
                    }
                }
            }
            Lam(var_name, var_t, bod) => {
                gamma.push((var_name.clone(), var_t));
                let bod_t = self.get_type(gamma, bod);
                gamma.pop();
                let bod_t = bod_t?;
                Ok(self.insert_node(Pi(var_name, var_t, bod_t)))
            }
            App(u, v) => {
                let u_t = self.get_type(gamma, u)?;
                let u_t = self.deep_copy(u_t);
                let u_t = self.unfold_constants(u_t).unwrap();
                self.beta_reduction(u_t);
                match get_node!(self, u_t) {
                    Pi(var_name, var_t, bod) => {
                        let v_t = self.get_type(gamma, v)?;
                        self.subtype(gamma, v_t, &mut gamma.clone(), var_t).map(|_| {
                            let bod =self.deep_copy(bod);
                            let v = self.deep_copy(v);
                            let otp_t = self.replace(bod, v);
                            let otp_t = self.insert_node(otp_t);
                            otp_t
                        })
                    }
                    _ => {
                        let u_t_string = self.lambda_to_string_with_context(u_t, gamma);
                        let msg = format!("Invalid left operand of an application : {u_t_string}");
                        Err(TypeIncoherence(msg))
                    }
                }
            }
            Let(var_name, var_t, e1, e2) => {
                gamma.push((var_name.clone(), var_t));
                let e1_t = self.get_type(gamma, e1);
                gamma.pop();
                let e1_t = e1_t?;
                gamma.push((var_name, e1_t));
                let e2_t = self.get_type(gamma, e2);
                gamma.pop();
                e2_t
            },
            Prop => Ok(self.insert_node(Type(1))),
            Type(i) => Ok(self.insert_node(Type(i + 1))),
            Hole => Err(TypeIncoherence(String::from(
                "impossible to infer a type for a hole",
            ))),
            Inductive(name) => {
                let inductive_data = self.inductives.get(&name).ok_or(UnknowInductive(var_to_string(&name)))?;
                Ok(inductive_data.type_of)
            },
            Constr(_, _, t) => Ok(self.deep_copy(t)),
            Match(t, x, p, r, v) => self.get_pattern_match_type(gamma, t, x, p, r, v),
            Fix(name,args,stru,tp,body) => {
                //println!("todo: recursivity structural condition");

                // adding each argument to gamma
                args.iter().for_each(|(name,e)|gamma.push((name.clone(),*e)));
                let mut tp_gamma = gamma.clone(); // store the gamma without recursive def for checking with tp

                // adding the type of the function to gamma
                let mut overall_type = tp.clone();
                args.iter().rev().for_each(|(name,expr)| {
                    let e = self.deep_copy(*expr);
                    overall_type = self.insert_node(Pi(name.clone(),e,overall_type))
                });
                gamma.push((name.clone(), overall_type));

                // trying to type body with new gamma -> if it's a subtype of tp, then it has type overall_type
                let body_t = self.get_type(gamma, body)
                    .and_then(|body_t| self.subtype(gamma, body_t, &mut tp_gamma, tp))
                    .map(|()| overall_type);        
                gamma.truncate(gamma.len()-1-args.len());
                body_t
            }
        }
    }

    /// returns the type of a pattern match ``Match(t, x, p, r, v)`` in context ``gamma``
    /// as with get_type, although gamma is borrowed as mutable, it will
    /// be returned as it was provided, even if an error occurs
    fn get_pattern_match_type(
        &mut self,
        gamma:&mut TypingContext,
        t:NodeIndex,
        x:VariableName,
        p:Pattern,
        r:NodeIndex,
        v:Vec<(Pattern, NodeIndex)>
    ) -> Result<NodeIndex, TypingError> {
        use LambdaNode::*;
        let t_type = self.get_type(gamma, t)?;

        // we retrieve the parameters and arguments of t
        let mut params_and_args = Vec::new();
        let mut t_type_copy = self.deep_copy(t_type);
        while let App(u, v) = get_node!(self, t_type_copy) {
            params_and_args.push(v);
            t_type_copy = u;
        }
        params_and_args.reverse();
        
        // we now look at the left over term, which should be the inductive
        // we retrieve the name, and hence the inductive data
        let ind_name = match get_node!(self, t_type_copy) {
            Inductive(ind_name) => ind_name,
            _ => return Err(MatchNonInductive(self.lambda_to_string_with_context(t_type, gamma))),
        };
        let ind_data = self.inductives[&ind_name].clone();

        // we check that p is valid, for that, we retrieve its arguments
        let mut p_copy = p.clone();
        let mut p_args_rev = Vec::new();
        while let Pattern::App(u, v) = p_copy {
            p_args_rev.push(*v);
            p_copy = *u;
        }
        // we check that we have ignored the arguments of the inductive
        for _ in 0..ind_data.parameters.len() {
            match p_args_rev.pop() {
                Some(Pattern::Var(name)) if name == (String::from(""), 0) => (),
                Some(Pattern::Var(name)) => return Err(InvalidPatternMatching(format!("not allowed to capture a parameter {}", var_to_string(&name)))),
                p => return  Err(InvalidPatternMatching(format!("patterns should be applications of a constructor to variables, encountered {p:?}"))),
            }
        }
        // we can now reverse, and obtain the arguments of the constructor in order
        let mut p_ind_args = Vec::new();
        for pat in p_args_rev.into_iter().rev() {
            match pat {
                Pattern::Var(name) => p_ind_args.push(name),
                p => return  Err(InvalidPatternMatching(format!("patterns should be applications of a constructor to variables, encountered {p:?}"))),
            }
        }

        // we now type the return type
        // we must push ALL the arguments, and then the type of t with arguments replaced by variables
        for (name, arg) in zip(&p_ind_args, &params_and_args[ind_data.parameters.len()..]) {
            let ty = self.get_type(gamma, *arg)?;
            gamma.push((name.clone(), ty))
        }
        ;
        // we must now push x as I pars var(n-1) .. var(0)
        // where n is the number of arguments
        if x != (String::from("_"), 0) {
            let mut x_ty = self.insert_node(Inductive(ind_name.clone()));
            for (i, param) in params_and_args.iter().enumerate() {
                if i < ind_data.parameters.len() {
                    // this is a parameter
                    x_ty = self.insert_node(App(x_ty, *param));
                } else {
                    // this is an argument
                    let var = self.insert_node(Var(params_and_args.len()-i-1));
                    x_ty = self.insert_node(App(x_ty, var));
                }
            }
            gamma.push((x.clone(), x_ty));
        }
        // before typing r, it may have expected less arguments (we may have ignored some arguments of the inductive)
        // so we may need to correct for that
        let r = self.deep_copy(r);
        self.shift_index_overwrite((p_ind_args.len()-p.bound_vars().len()) as isize, r);

        // we now type r
        let r_t = self.get_type(gamma, r);
        let r_t_str = r_t.clone().map(|r_t| self.lambda_to_string_with_context(r_t, gamma));
        if x != (String::from("_"), 0) {gamma.pop();}
        gamma.truncate(gamma.len()-p_ind_args.len());
        let r_t = r_t?;
        let r_t_str = r_t_str?;

        // we check that this is a valid sort
        // checking that we are a type is a bit of a hack, I know
        let prop = self.insert_node(Prop);
        let type_max = self.insert_node(Type(usize::MAX));
        // getting the sort of the inductive
        let mut ind_sort = ind_data.type_of;
        while let Pi(_, _, body) = get_node!(self, ind_sort) {ind_sort = body}
        if ind_data.elim == Eliminability::Uneliminable && self.subtype(gamma, r_t, &mut Vec::new(), prop).is_err() {
            return Err(InvalidElimination(r_t_str))
        }

        // we will now type each branch and check exhaustiveness
        if v.len() != ind_data.constructors.len() {
            return Err(InvalidPatternMatching(self.lambda_to_string_with_context(t, gamma)))
        }
        for (i, ((pi, ei), (c_name, c_ty))) in zip(v, ind_data.constructors).enumerate() {
            let mut c_ty = self.deep_copy(c_ty); // we deepcopy, as we will modify
            // first, we  analyse the pattern to check it is the proper constructor applied to some arguments
            let mut pi_copy = pi.clone();
            let mut pi_args_rev = Vec::new();
            while let Pattern::App(u, v) = pi_copy {
                pi_args_rev.push(*v);
                pi_copy = *u;
            }
            // at that point, we must have the proper constructor
            match pi_copy {
                Pattern::Constr(p_cons_i, ref p_ind_name) if p_cons_i == i && *p_ind_name == ind_name => (),
                _ => panic!("invalid pattern, either not a constructor, or not the good one (currently, constructors must all be given, and in the same order as the inductive definition"),
            }

            // we start scanning the arguments of the pattern, to check that the first ones (corresponding to parameters)
            for param in &params_and_args[..ind_data.parameters.len()] {
                match pi_args_rev.pop() {
                    Some(Pattern::Var(name)) if name == (String::from(""), 0) => (),
                    Some(Pattern::Var(name)) => return Err(InvalidPatternMatching(format!("not allowed to capture a parameter {}", var_to_string(&name)))),
                    p => return  Err(InvalidPatternMatching(format!("patterns should be applications of a constructor to variables, encountered {p:?}"))),
                }
            }
            // we now substitue the concrete parameters in the constructor type
            // as parameters may depend on each other, we have to substitute in the others at each step
            // this means we do a full copy of the parameters
            let parameters : Vec<_> = params_and_args[..ind_data.parameters.len()].iter().map(|node| self.deep_copy(*node)).collect();
            for param in parameters.iter() {
                match get_node!(self, c_ty) {
                    Pi(_, _, body) => c_ty = self.replace_keep(body, *param),
                    _ => panic!("constructor's type invalid with respect to inductive parameters"),
                }
            }

            // we now retrieve the (type of the) arguments of the constructor
            // at the same time, we finish scanning the pattern and ensure it
            // had the proper number of arguments
            let mut pi_cons_args_ty = Vec::new();
            while let Pi(_, var_ty, body) = get_node!(self, c_ty) {
                let var_name = match pi_args_rev.pop() {
                    Some(Pattern::Var(name)) => name,
                    None => return  Err(InvalidPatternMatching(format!("pattern in branch {i} was not provided enough arguments"))),
                    Some(p) => return  Err(InvalidPatternMatching(format!("patterns should be applications of a constructor to variables, encountered {p}"))),
                };
                pi_cons_args_ty.push((var_name.clone(), var_ty)); // we use the name used in the pattern
                c_ty = body;
            }
            if pi_args_rev.len() != 0 {
                return Err(InvalidPatternMatching(format!("pattern matching in branch {i} was provided too much arguments")))
            }
            
            // we now push them, after the parameters
            // of course, we only push bound vars
            // we will also need to offset the free vars as these arguments
            // were defined while expecting all arguments to be bound
            // we must keep track of how many args were bound compared to how many there was
            let mut n_bound_before = 0;
            let mut n_args_before = 0;
            pi_cons_args_ty
                .iter()
                .for_each(|(name, node)| {
                    if *name != (String::from(""), 0) {
                        let node = self.deep_copy(*node);
                        self.shift_index_overwrite(n_bound_before-n_args_before, node);
                        gamma.push((name.clone(), node));
                        n_bound_before += 1;
                    }
                    n_args_before += 1;
                    let temp = self.insert_node(Var(0));
                    let temp = self.get_type(gamma, temp).unwrap();
                });

            // we must now build the target type of the right expression
            // it will be built out of r, while replacing some of its parameters
            let mut target_type = self.deep_copy(r);
            // first, we must build the value of x (if needed)
            if x.0 != String::from("_") {
                let mut x_val = self.insert_node(Constr(i, ind_name.clone(), c_ty));
                // step 1 : substitue the actual values of the parameters
                for param in params_and_args[..ind_data.parameters.len()].iter() {
                    x_val = self.insert_node(App(x_val, *param))
                }
                // step 2 : substitute the value of the arguments, as variable whose type will
                // be provided later in the context
                for i in (0..pi_cons_args_ty.len()).rev() {
                    let var = self.insert_node(Var(i));
                    x_val = self.insert_node(App(x_val, var));
                }
                // not sure what I'm doing, but this might work :
                self.shift_index_overwrite(0 - pi.bound_vars().len() as isize, x_val);
                // we can now use x
                target_type = self.replace_keep(r, x_val);
            }
            // we must now provide the Inductive's arguments in this constructor to the target_type
            // conveniently, c_ty contains the resulting type of this constructor
            // we extract everything, including parameters and filter afterwards
            let mut cons_params_and_args = Vec::new();
            while let App(u, v) = get_node!(self, c_ty) {
                cons_params_and_args.push(v);
                c_ty = u;
            }
            cons_params_and_args.reverse();
            
            // we can now substitue the arguments, or at least those that were bound
            for (pat_var, arg) in zip(&p_ind_args, &cons_params_and_args[ind_data.parameters.len()..]) {
                if pat_var.0 != "" {target_type = self.replace_keep(target_type, *arg)}
            }
            // there is still a catch, p has defined some vars that were not taken into account
            // when we were defining r, so we need to offset
            self.shift_index_overwrite(pi.bound_vars().len() as isize, target_type);
            let otp = self.typecheck_with_variables_context(gamma, ei, target_type);
            gamma.truncate(gamma.len()-pi.bound_vars().len());
            otp?
        }
        // we can now substitute the final values of x (if bound) and the bound vars of p 
        let mut r = self.deep_copy(r);
        if x.0 != String::from("_") {r = self.replace_keep(r, t)}
        for (var, ty) in zip(&p_ind_args, &params_and_args[ind_data.parameters.len()..]) {
            if var.0 != String::from("") {r = self.replace_keep(r, *ty)}
        }
        Ok(r)
    }

    /// Implements the subtype relation
    /// it assumes that its argument are beta reduced
    pub fn subtype(
        &mut self,
        gamma1: &mut TypingContext,
        t1: NodeIndex,
        gamma2: &mut TypingContext,
        t2: NodeIndex,
    ) -> Result<(), TypingError> {
        use LambdaNode::*;
        if self.deep_equality_with_contexts(gamma1, t1, gamma2, t2)? {return Ok(());}
        match (get_node!(self, t1), get_node!(self, t2)) {
            // we must correct for the fact that our context might differ
            // the interpretation of a De Bruijn index is dependent on the len of the context
            (Var(i), Var(j)) if i + gamma2.len() == j + gamma1.len() => Ok(()),
            (Const(name), _) => {
                let c = self.constants[&name].0;
                self.subtype(gamma1, c, gamma2, t2)
            },
            (_, Const(name)) => {
                let c = self.constants[&name].0;
                self.subtype(gamma1, t1, gamma2, c)
            },
            (Inductive(name), _) => {
                // we need to get the full type
                self.subtype(gamma1, self.inductives[&name].type_of, gamma2, t2)
            },
            (_, Inductive(name)) => {
                // we need to get the full type
                self.subtype(gamma1, t1, gamma2, self.inductives[&name].type_of)
            },
            (Constr(_, _, t1), _) => self.subtype(gamma1, t1, gamma2, t2),
            (_, Constr(_, _, t2)) => self.subtype(gamma1, t1, gamma2, t2),
            (Prop, Prop) => Ok(()),
            (Prop, Type(i)) if i >= 1 => Ok(()),
            (Type(i), Type(j)) if i <= j => Ok(()),
            (Pi(var_name1, tvar1, tbod1), Pi(var_name2, tvar2, tbod2)) => {
                    self.subtype(gamma1, tvar2, gamma2, tvar1)?;
                    gamma1.push((var_name1, tvar1));
                    gamma2.push((var_name2, tvar2));
                    let otp = self.unify(gamma1, tbod1, gamma2, tbod2);
                    gamma1.pop();
                    gamma2.pop();
                    otp
            },
            _ => {
                let t1_string = self.lambda_to_string_with_context(t1, gamma1);
                let t2_string = self.lambda_to_string_with_context(t2, gamma2);
                Err(SubtypingFail(t1_string, t2_string))
            }
        }
    }

    pub fn unify(
        &mut self,
        gamma1: &mut TypingContext,
        t1: NodeIndex,
        gamma2: &mut TypingContext,
        t2: NodeIndex,
    ) -> Result<(), TypingError> {
        if self.deep_equality_with_contexts(gamma1, t1, gamma2, t2)? {
            Ok(())
        } else {
            let t1_string = self.lambda_to_string_with_context(t1, gamma1);
            let t2_string = self.lambda_to_string_with_context(t2, gamma2);
            Err(UnificationFail(t1_string, t2_string))
        }
    }

}

#[cfg(test)]
mod tests {
    use crate::definitions::*;
    use crate::errors::TypingError::*;
    use LambdaTerm::*;

    macro_rules! assert_type {
        ($term:tt, $target_type:tt) => {{
            // we have a scope for the lock
            let mut proof = GlobalContext::new();
            let term = proof.insert_term($term).unwrap();
            let target_type = proof.insert_term($target_type).unwrap();
            match proof.typecheck_with_variables_context(&mut Vec::new(), term, target_type) {
                Ok(()) => (),
                Err(e) => panic!("{e}")
            }
        }};
    }

    #[test]
    pub fn basic() {
        let term = Abstraction(
            (String::from("x"), 0),
            Box::new(Prop),
            Box::new(Variable(("x".to_owned(), 0))),
        );
        let ty = Pi(
            (String::from("x"), 0),
            Box::new(Prop),
            Box::new(Prop)
        );
        assert_type!(term, ty);
    }

    #[test]
    pub fn universes() {
        let term = Prop;
        let ty = Type(1);
        assert_type!(term, ty);
        let term = Type(165);
        let ty = Type(166);
        assert_type!(term, ty);
        let term = Type(1);
        let ty = Type(2);
        assert_type!(term, ty);
    }

    #[test]
    pub fn universes_error() {
        let mut proof = GlobalContext::new();

        let term = Prop;
        let ty = Type(0);
        let term = proof.insert_term(term).unwrap();
        let ty = proof.insert_term(ty).unwrap();
        let error = Err(SubtypingFail(String::from("Type(1)"), proof.lambda_to_string(ty)));
        let otp = proof.typecheck_with_variables_context(&mut Vec::new(), term, ty);
        assert_eq!(otp, error);
    
        let term = Type(9784);
        let ty = Type(8);
        let term = proof.insert_term(term).unwrap();
        let ty = proof.insert_term(ty).unwrap();
        let error = Err(SubtypingFail(String::from("Type(9785)"), proof.lambda_to_string(ty)));
        let otp = proof.typecheck_with_variables_context(&mut Vec::new(), term, ty);
        assert_eq!(otp, error);

        let term = Type(8);
        let ty = Type(8);
        let term = proof.insert_term(term).unwrap();
        let ty = proof.insert_term(ty).unwrap();
        let error = Err(SubtypingFail(String::from("Type(9)"), proof.lambda_to_string(ty)));
        let otp = proof.typecheck_with_variables_context(&mut Vec::new(), term, ty);
        assert_eq!(otp, error);
    }

    #[test]
    pub fn prop_to_prop() {
        let term = Abstraction(
            (String::from("x"), 0),
            Box::new(Prop),
            Box::new(Variable((String::from("x"), 0)))
        );
        let ty = Pi(
            (String::from(""), 0),
            Box::new(Prop),
            Box::new(Prop)
        );
        assert_type!(term, ty);
    }

    #[test]
    pub fn functions() {
        let term = Abstraction(
            (String::from("f"), 0),
            Box::new(Pi(
                (String::from("x"), 0),
                Box::new(Prop),
                Box::new(Prop)
            )),
            Box::new(Abstraction(
                (String::from("x"), 0),
                Box::new(Prop),
                Box::new(Application(
                    Box::new(Variable((String::from("f"), 0))),
                    Box::new(Variable((String::from("x"), 0)))
                ))
            ))
        );
        let ty = Pi(
            (String::from("f"), 0),
            Box::new(Pi(
                (String::from("x"), 0),
                Box::new(Prop),
                Box::new(Prop)
            )),
            Box::new(Pi(
                (String::from("x"), 0),
                Box::new(Prop),
                Box::new(Prop)
            ))
        );
        assert_type!(term, ty);
    }

    #[test]
    pub fn foralla_a_implies_a() {
        let term = Abstraction(
            (String::from("A"), 0),
            Box::new(Prop),
            Box::new(Abstraction(
                (String::from("x"), 0),
                Box::new(Variable((String::from("A"), 0))),
                Box::new(Variable((String::from("x"), 0)))
            ))
        );
        let ty = Pi(
            (String::from("A"), 0),
            Box::new(Prop),
            Box::new(Pi(
                (String::from("x"), 0),
                Box::new(Variable((String::from("A"), 0))),
                Box::new(Variable((String::from("A"), 0)))
            ))
        );
        assert_type!(term, ty);
    }

    #[test]
    pub fn skipped_var() {
        let term = Abstraction(
            (String::from("A"), 0),
            Box::new(Prop),
            Box::new(Abstraction(
                (String::from("B"), 0),
                Box::new(Prop),
                Box::new(Abstraction(
                    (String::from("x"), 0),
                    Box::new(Variable((String::from("A"), 0))),
                    Box::new(Variable((String::from("x"), 0)))
                ))
            ))
        );
        let ty = Pi(
            (String::from("A"), 0),
            Box::new(Prop),
            Box::new(Pi(
                (String::from("B"), 0),
                Box::new(Prop),
                Box::new(Pi(
                    (String::from("x"), 0),
                    Box::new(Variable((String::from("A"), 0))),
                    Box::new(Variable((String::from("A"), 0)))
                ))
            ))
        );
        assert_type!(term, ty);
    }

    #[test]
    pub fn prop_impredicativity() {
        let term = Pi(
            (String::from("x"), 0),
            Box::new(Prop),
            Box::new(Pi(
                (String::from("_"), 0),
                Box::new(Variable((String::from("x"), 0))),
                Box::new(Variable((String::from("x"), 0)))
            ))
        );
        let ty = Prop;
        assert_type!(term, ty);
    }

    #[test]
    pub fn type_predicativity() {
        let term = Pi(
            (String::from("x"), 0),
            Box::new(Type(0)),
            Box::new(Pi(
                (String::from(""), 0),
                Box::new(Variable((String::from("x"), 0))),
                Box::new(Variable((String::from("x"), 0)))
            ))
        );
        let ty = Type(1);
        assert_type!(term, ty);

        let mut proof = GlobalContext::new();
        let term = Pi(
            (String::from("x"), 0),
            Box::new(Type(0)),
            Box::new(Pi(
                (String::from(""), 0),
                Box::new(Variable((String::from("x"), 0))),
                Box::new(Variable((String::from("x"), 0)))
            ))
        );
        let ty = Type(0);
        let term = proof.insert_term(term).unwrap();
        let ty = proof.insert_term(ty).unwrap();
        let error = Err(SubtypingFail(
            String::from("Type(1)"),
            proof.lambda_to_string(ty)
        ));
        let otp = proof.typecheck_with_variables_context(&mut Vec::new(), term, ty);
        assert_eq!(otp, error);
    }


    #[test]
    /// checks that we take into acount free variables
    pub fn free_vars() {
        let mut proof = GlobalContext::new();
        let term = Variable((String::from("x"), 0));
        let ty = Type(64);

        let mut insert_ctx = vec![(String::from("x"), 0)];
        let term = proof.insert_term_ctx(term, &mut insert_ctx).unwrap();
        let ty = proof.insert_term(ty).unwrap(); // we insert a close term, no need for the context
        
        let mut ctx = vec![((String::from("x"), 0), ty)];
        assert!(proof.typecheck_with_variables_context(&mut ctx, term, ty).is_ok());
    }

    #[test]
    pub fn free_vars2() {
        let mut proof = GlobalContext::new();
        let term = Variable((String::from("x"), 1));
        let ty = Type(64);
        let ty_other = Prop;

        let mut insert_ctx = vec![(String::from("x"), 2), (String::from("x"), 1), (String::from("x"), 0)];
        let term = proof.insert_term_ctx(term, &mut insert_ctx).unwrap();
        let ty = proof.insert_term(ty).unwrap(); // we insert a close term, no need for the context
        let ty_other = proof.insert_term(ty_other).unwrap(); // we insert a close term, no need for the context
        
        let mut ctx = vec![((String::from("x"), 2), ty_other), ((String::from("x"), 1), ty), ((String::from("x"), 0), ty_other)];
        assert!(proof.typecheck_with_variables_context(&mut ctx, term, ty).is_ok());
    }


    #[test]
    pub fn inductive() { // todo
        let term = Abstraction(
            (String::from("x"), 0),
            Box::new(Prop),
            Box::new(Variable(("x".to_owned(), 0))),
        );
        let ty = Pi(
            (String::from("x"), 0),
            Box::new(Prop),
            Box::new(Prop)
        );
        assert_type!(term, ty);
    }
}
