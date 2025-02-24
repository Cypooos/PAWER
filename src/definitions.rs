use std::{collections::HashMap, fmt::Display};
use std::fmt;

use crate::errors::{InternalError, Error};

// This file defines very important concept like the LambdaTerm, LambdaNode, ProofInfo, HoleContext, InductiveData, Pattern and the GeneralCOntext structures


pub type DeBruijnIndex = usize;
pub type VariableName = (String, usize);
pub type NodeIndex = usize;

/// type of a context for a goal
/// this contains a list of variables/hypothesis of the form
/// (var_name, type_node_index)
pub type VariablesContext = Vec<(VariableName, NodeIndex)>;

/// A typing context, it maps variables to their current type
/// It uses DeBruijn indices, and the variable of DeBruijn index 0 is the last element of the vector
pub type TypingContext = Vec<(VariableName, NodeIndex)>;


pub fn var_to_string(var: &VariableName) -> String {
    if var.0 == "" && var.1 == 0 {
        format!("_")
    } else if var.1 == 0 {
        format!("{}", var.0)
    } else {
        format!("{}{}", var.0, var.1)
    }
}

// Information about our current proof
#[derive(Debug, Eq, PartialEq, Clone)]
pub struct ProofInfo{
    pub name:Option<VariableName>, // if we are using `Theorem` or `Definition`, the name. With `Goal` it will be set to None
    pub prop:NodeIndex, // The thing we are proving
    pub root:NodeIndex, // Root node of the proof
}

impl ProofInfo {
    pub fn new(name:Option<VariableName>, prop:NodeIndex, root:NodeIndex) -> Self {
        Self { name, prop, root }
    }
}

/// Lambda term as an AST for parsing and tactics inputs
#[allow(dead_code)]
#[derive(Debug, Eq, PartialEq, Clone)]
pub enum LambdaTerm {
    Variable(VariableName),
    Abstraction(VariableName, Box<LambdaTerm>, Box<LambdaTerm>), // `fun (name:type) => code` is Abstraction(name, type, code) 
    Application(Box<LambdaTerm>, Box<LambdaTerm>),
    Pi(VariableName, Box<LambdaTerm>, Box<LambdaTerm>), // `forall (name:type), code` is Pi(name, type, code) 
    Let( // not implemented
        VariableName,
        Box<LambdaTerm>,
        Box<LambdaTerm>,
        Box<LambdaTerm>,
    ),
    // `fix name <args> {struct arg} : type := code` is Fix(name, args, arg, type, code)
    Fix(VariableName, Vec<(VariableName,LambdaTerm)>, VariableName, Box<LambdaTerm>, Box<LambdaTerm>),
    Set, // Set = Type(0)
    Prop,
    Type(usize),
    /// Constr(i, I, t) is the i-th constructor of inductive type I, it has type t
    Constr(usize, VariableName, Box<LambdaTerm>),
    /// Match(t, x, p, r, v=vec![(pi, ei)_{i}]) corresponds to
    /// match t as x in p return r with
    /// | pi => ei
    /// ...
    /// end
    /// t is the term we are matching
    /// x is a variable name we give it
    /// p is the pattern that matches the type of t, it is an inductive type
    /// and its use is to extract some parameters of the type
    /// r is the type of the returned expression, it can use the variables bound by p
    /// v contains all the branches, pi being the pattern, and ei the expression
    ///     ei can use the variables bound by the corresponding pi, it cannot use the
    ///     variables bound by p
    Match(Box<LambdaTerm>, VariableName, Pattern, Box<LambdaTerm>, Vec<(Pattern, LambdaTerm)>),
}

impl LambdaTerm {

    /// tell if `name` is in the free variables of self.
    /// Is used for printing reason to decided beetween `A -> B` and `forall (name:A), B`
    pub fn is_used_var(&self, name: &VariableName) -> bool {
        match self {
            Self::Variable(x) => x == name,
            Self::Set | Self::Prop | Self::Type(_) => false,
            Self::Abstraction(n, a, _) | Self::Pi(n, a, _) if n == name => a.is_used_var(name),
            Self::Let(n, a, b, _) if n == name => a.is_used_var(name) || b.is_used_var(name),
            Self::Abstraction(_, a, b) | Self::Pi(_, a, b) | Self::Application(a, b) => {
                a.is_used_var(name) || b.is_used_var(name)
            }
            Self::Let(_, a, b, c) => {
                a.is_used_var(name) || b.is_used_var(name) || c.is_used_var(name)
            }
            Self::Fix(n, vars, _, ty, _) if name == n || vars.iter().any(|(a,_)|a==name) => {
                ty.is_used_var(name) || vars.iter().any(|(_,a)| a.is_used_var(name))
            }
            Self::Fix(_, vars, _, ty, lamb) => {
                ty.is_used_var(name) || vars.iter().any(|(_,a)| a.is_used_var(name)) || lamb.is_used_var(name)
            }
            Self::Constr(_, _, t) => t.is_used_var(name),
            Self::Match(t, _, _, r, v) =>
                t.is_used_var(name) || r.is_used_var(name) || v.iter().any(|(_, ti)| ti.is_used_var(name)),
        }
    }
}

impl fmt::Display for LambdaTerm {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use LambdaTerm::*;
        fn aux(curr: &LambdaTerm, prio: usize) -> String {
            match curr {
                Variable(x) => var_to_string(x),
                Pi(n, a, b) if prio <= 10 && b.is_used_var(n) => {
                    format!("∀ {}:{}, {}", var_to_string(n), aux(a, 0), aux(b, 10))
                }
                Pi(n, a, b) if prio <= 20 && !b.is_used_var(n) => {
                    format!("{} -> {}", aux(a, 21), aux(b, 20))
                }
                Abstraction(n, a, b) if prio <= 60 => {
                    format!("fun ({}:{}) => {}", var_to_string(n), aux(a, 0), aux(b, 60))
                }
                Let(n, a, b, c) if prio <= 70 => format!(
                    "let ({}:{}) = {} in {}",
                    var_to_string(n),
                    aux(a, 0),
                    aux(b, 70),
                    aux(c, 70)
                ),
                Application(a, b) if prio <= 90 => format!("{} {}", aux(a, 91), aux(b, 90)),
                Prop => format!("Prop"),
                Type(i) => format!("type ({i})"),
                Set => format!("Set"),
                Fix(name,vars, stru, ty, lamb) if prio <= 60  => 
                    format!("fix {} {} {{struct {}}} : {} := {}",
                    var_to_string(name),
                    vars.iter().fold(format!(""),|stri,(a,b)|format!("{stri} ({}:{})",var_to_string(a),aux(b,0))),
                    var_to_string(stru), aux(ty, 0), aux(lamb, 0)),
                Pi(..) | Abstraction(..) | Let(..) | Application(..) => format!("({})", aux(curr, 0)),
                Match(t, x, p, r, v) => {
                    let mut branches = String::new();
                    for (pi, ei) in v { branches.push_str(format!("| {pi} => {ei}\n").as_str());}
                    format!("match {} as {} in {} return {} with {} end",
                    t,
                    var_to_string(x),
                    p,
                    r,
                    branches
                    )
                },
                Constr(i, ty_name, _) => format!("Constr({i}, {}", var_to_string(ty_name)),
                Fix(..) => todo!("print fix"),
            }
        }
        write!(f, "{}", aux(&self, 0))
    }
}

#[derive(Debug, Clone, Eq, PartialEq, Hash)]
/// context of a Hole, i.e. a goal
pub struct HoleContext {
    /// type of the proof, given as the corresponding NodeIndex
    pub goal: NodeIndex,
    /// NodeIndex of where the proof is to be placed
    pub node: NodeIndex,
    /// the context of this goal, i.e. the list of local variables/hypothesis
    /// of the form (var_name, type_node_index)
    pub context: VariablesContext,
}

impl HoleContext {
    pub fn new(goal: NodeIndex, node:NodeIndex) -> Self {
        Self {
            goal,
            node,
            context: Vec::new(),
        }
    }
}

#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub enum LambdaNode {
    Var(DeBruijnIndex),
    Const(VariableName),
    /// Pi(name, type, expr)
    Pi(VariableName, NodeIndex, NodeIndex),
    /// Lam(name, type, expr)
    Lam(VariableName, NodeIndex, NodeIndex),
    App(NodeIndex, NodeIndex),
    /// not implemented
    Let(VariableName, NodeIndex, NodeIndex, NodeIndex),
    Prop,
    Type(usize),

    /// hole for a proof
    Hole,

    /// term representing an inductive
    Inductive(VariableName),

    /// Constr(i, I, t) is the i-th constructor of inductive type I and it has type t
    Constr(usize, VariableName, NodeIndex),

    /// Match(t, x, p, r, v=vec![(pi, ei)_{i}]) corresponds to
    /// match t as x in p return r with
    /// | pi => ei
    /// ...
    /// end
    /// - t is the term we are matching
    /// - x is a variable name we give it
    /// - p is the pattern that matches the type of t, it is an inductive type
    /// and its use is to extract some parameters of the type
    /// - r is the type of the returned expression, it can use the variables bound by p
    /// - v contains all the branches, pi being the pattern, and ei the expression
    ///     ei can use the variables bound by the corresponding pi, it cannot use the
    ///     variables bound by p
    /// 
    /// **important remarks**:
    /// regarding variables, do note that patterns bind variables, so Debruijn indices are impacted by that
    /// in particular, when looking at the the return clause, the variables of the type pattern are bound,
    /// when in a branch, the variable of the associated pattern are bound (but not the one of the type pattern)
    Match(NodeIndex, VariableName, Pattern, NodeIndex, Vec<(Pattern, NodeIndex)>),

    // `fix name <args> {struct arg} : type := code` is Fix(name, args, arg, type, code)
    Fix(VariableName, Vec<(VariableName,NodeIndex)>, VariableName, NodeIndex, NodeIndex),
}

// The structure for a singl case of pattern-matching of a match for example
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Pattern {
    /// During parsing, constructors are consider as variables
    /// Wilcard is the empty variable
    Var(VariableName),
    /// Constructor are converted from Var when being inserted into the memory
    /// Constr(i, I) is the i-th constructor of type I
    Constr(usize, VariableName),
    /// constant
    Const(VariableName),
    /// inductive
    Inductive(VariableName), 
    // Rename(Box<Pattern>, VariableName),
    App(Box<Pattern>, Box<Pattern>),
}

impl Display for Pattern{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self{
            Pattern::Var(name) => write!(f, "{}", var_to_string(name)),
            Pattern::Constr(i, big_i) => write!(f, "Constr({}, {})", i, var_to_string(big_i)),
            Pattern::App(l, r) => write!(f, "({} {})", l, r),
            Pattern::Const(name) => write!(f, "constant({})", var_to_string(name)),
            Pattern::Inductive(name) => write!(f, "Inductive({})", var_to_string(name)),
        }
    }
}

impl Pattern {

    // Return the list of free variables of the pattern using an accumulator (see `bound_vars`)
    fn bound_vars_aux(&self, mut acc:Vec<VariableName>) -> Vec<VariableName> {
        match self {
            Self::Var(v) if *v != (String::from(""), 0)=> {
                acc.push(v.clone());
                acc
            },
            Self::Var(_) | Self::Constr(..) | Self::Const(_) | Self::Inductive(_) => acc,
            Self::App(p1, p2) => {
                let acc = p1.bound_vars_aux(acc);
                p2.bound_vars_aux(acc)
            },
        }
    }

    /// returns the vector of variables bound by a pattern
    pub fn bound_vars(&self) -> Vec<VariableName> {
        self.bound_vars_aux(Vec::new())
    }


    /// returns the number of binds done by this patterns
    /// this includes wildcard binds
    pub fn n_bind(&self) -> usize {
        match self {
            Self::Var(v) if *v != (String::from(""), 0) => 1,
            Self::Var(_) | Self::Constr(..) | Self::Const(_) | Self::Inductive(_) => 0,
            Self::App(p1, p2) => {
                p1.n_bind()+p2.n_bind()
            },
        }
    }

}

/// A structure indicating if a particular inductive is eliminable (can be match on) or not
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum Eliminability {
    #[default] Eliminable,
    Uneliminable,
}

/// A structure to represent an inductive data 
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct InductiveData {
    /// list of the inductive's parameters with their type
    pub parameters: Vec<(VariableName, NodeIndex)>,
    /// the type of the inductive, it contains the parameters
    /// it is Pi param, ar
    /// where ar is the arity
    pub type_of: NodeIndex,
    /// list of the Inductive's constructors
    /// `constructors[i] = (Ci, ti)` corresponds to the i-th construct
    /// its name is Ci and its type is ti
    pub constructors: Vec<(VariableName, NodeIndex)>,
    /// this specifies if the inductive can be elimined in a matching or not
    pub elim: Eliminability,
}

impl InductiveData {
    pub fn new(
        parameters: Vec<(VariableName, NodeIndex)>,
        type_of: NodeIndex,
        constructors: Vec<(VariableName, NodeIndex)>,
        elim: Eliminability,
    ) -> Self {
        Self { parameters, type_of, constructors, elim }
    }
}

#[derive(Debug, Clone)]
/// Contains all information about the inner state of the proof system. It's the "manager".
/// Since a lot of other structure relies on the GlobalContext to be printed (like LambdaNode), this structure contains also a lot of `<type>_to_string` functions
pub struct GlobalContext {
    /// inner storage for all the lambda terms
    pub lambda_storage: Vec<LambdaNode>,
    /// list of current goals
    pub goals: Vec<HoleContext>,
    /// list of the current constants
    /// constants["add"] = (def, type)  (both as node indices)
    pub constants: HashMap<VariableName, (NodeIndex, NodeIndex)>,
    /// if in proof mode, this contains info about the current proof
    /// this is not to be confused with the current goal/Hole
    /// the root corresponds to lam in Theorem lam.
    pub root: Option<ProofInfo>,
    /// Map associating to an inductive type the list of its constructor
    pub inductives: HashMap<VariableName, InductiveData>,
}

impl GlobalContext {
    /// inserts a term ``l`` with the variables names ``names``
    /// the variable names are given according to their DeBruijn indices
    /// i.e. ``Var(i)`` has name ``names[i]``
    /// do note that although ``names`` is borrowed as mutable, it will have
    /// the same content as before the call
    pub fn insert_term_ctx(&mut self, l: LambdaTerm, names: &mut Vec<VariableName>) -> Result<NodeIndex,Error> {
        use LambdaTerm::*;
        match l {
            Variable(name) => {
                let i = names
                    .iter()
                    .rev()
                    .enumerate()
                    .find(|(_, var_name)| **var_name == name);
                if let Some((i, _)) = i {
                    return Ok(self.insert_node(LambdaNode::Var(i)))
                }
                if let Some(_) = self.constants.get(&name) {
                    return Ok(self.insert_node(LambdaNode::Const(name)))
                }
                if let Some(_) = self.inductives.get(&name) {
                    return Ok(self.insert_node(LambdaNode::Inductive(name)))
                }
                if let Some((i, name, ty)) = self.is_cons(&name) {
                    return Ok(self.insert_node(LambdaNode::Constr(i, name, ty)))
                }

                Err(InternalError::InsertTermUnboundedVariable(var_to_string(&name)).into())


            }
            Abstraction(name, t, l) => {
                let t = self.insert_term_ctx(*t, names)?;
                names.push(name);
                let l = self.insert_term_ctx(*l, names)?;
                let name = names.pop().unwrap();
                Ok(self.insert_node(LambdaNode::Lam(name, t, l)))
            }
            Application(lhs, rhs) => {
                let lhs = self.insert_term_ctx(*lhs, names)?;
                let rhs = self.insert_term_ctx(*rhs, names)?;
                Ok(self.insert_node(LambdaNode::App(lhs, rhs)))
            }
            Pi(name, t, l) => {
                let t = self.insert_term_ctx(*t, names)?;
                names.push(name);
                let l = self.insert_term_ctx(*l, names)?;
                let name = names.pop().unwrap();
                Ok(self.insert_node(LambdaNode::Pi(name, t, l)))
            }
            Let(name, t, val, l) => {
                let t = self.insert_term_ctx(*t, names)?;
                let val = self.insert_term_ctx(*val, names)?;
                names.push(name);
                let l = self.insert_term_ctx(*l, names)?;
                let name = names.pop().unwrap();
                Ok(self.insert_node(LambdaNode::Let(name, t, val, l)))
            }
            Set => Ok(self.insert_node(LambdaNode::Type(0))),
            Prop => Ok(self.insert_node(LambdaNode::Prop)),
            Type(i) => Ok(self.insert_node(LambdaNode::Type(i))),
            Constr(n, i, t) => {
                let t = self.insert_term_ctx(*t, names)?;
                Ok(self.insert_node(LambdaNode::Constr(n, i, t)))
            }
            Match(t, x, p, r, v) => {
                let p = self.clean_pattern(p);
                let t = self.insert_term_ctx(*t, names)?;
                let mut p_vars = p.bound_vars();
                let n_p_vars = p_vars.len();
                names.append(&mut p_vars);
                if x.0 != String::from("_") {names.push(x.clone());}
                let r = self.insert_term_ctx(*r, names)?;
                if x.0 != String::from("_") {names.pop();}
                names.truncate(names.len()-n_p_vars);
                let mut v1 = Vec::new();
                for (pi, ti) in v {
                    let pi = self.clean_pattern(pi);
                    let mut pi_vars = pi.bound_vars();
                    let n_pi_vars = pi_vars.len();
                    names.append(&mut pi_vars);
                    v1.push((pi, self.insert_term_ctx(ti, names)?));
                    names.truncate(names.len()-n_pi_vars);
                }
                Ok(self.insert_node(LambdaNode::Match(t, x, p, r, v1)))
            }
            Fix(name,args,stru,ret_type,expr) => {

                let mut args_ins = Vec::new();
                for (name,code) in args {
                    let v = self.insert_term_ctx(code.clone(), names)?;
                    names.push(name.clone());
                    args_ins.push((name,v));
                }

                let ret_type_ins = self.insert_term_ctx(*ret_type, names)?;

                names.push(name.clone());
                let expr_ins = self.insert_term_ctx(*expr, names)?;
                names.truncate(names.len()-1-args_ins.len());

                Ok(self.insert_node(LambdaNode::Fix(name, args_ins, stru, ret_type_ins, expr_ins)))
            },
        }
    }

    /// inserts a closed term into the the proof context
    pub fn insert_term(&mut self, l: LambdaTerm) -> Result<NodeIndex,Error> {
        self.insert_term_ctx(l, &mut Vec::new())
    }

    /// Copy the root of `from` at position `to`.
    /// Used to replace a Hole with a term.
    pub fn merge_term(&mut self, from:NodeIndex, to:NodeIndex) {
        self.lambda_storage[to] = self.lambda_storage[from].clone()
    }

    /// Generate a new proof context
    pub fn new() -> GlobalContext {
        Self {
            lambda_storage: Vec::new(),
            goals: Vec::new(),
            constants: HashMap::new(),
            root: None,
            inductives: HashMap::new(),
        }
    }


    fn is_used_var_aux(&self, node: NodeIndex, indent: usize) -> bool {
        use LambdaNode::*;
        match match self.lambda_storage.get(node) {
            None => return false,
            Some(e) => e,
        } {
            Var(x) => *x == indent,
            Const(_) | Inductive(_) | Prop | Type(_) | Hole => false,
            App(a, b) => self.is_used_var_aux(*a, indent) || self.is_used_var_aux(*b, indent),
            Let(_, a, b, c) => {
                self.is_used_var_aux(*a, indent)
                    || self.is_used_var_aux(*b, indent)
                    || self.is_used_var_aux(*c, indent + 1)
            }
            Pi(_, a, b) | Lam(_, a, b) => {
                self.is_used_var_aux(*a, indent) || self.is_used_var_aux(*b, indent + 1)
            }
            Constr(_, _, t) => self.is_used_var_aux(*t, indent),
            Match(t, _, p, r, v) => {
                let n_p_vars = p.bound_vars().len();
                self.is_used_var_aux(*t, indent+n_p_vars) || self.is_used_var_aux(*r, indent) ||
                v.iter().any(|(pi, ei)| self.is_used_var_aux(*ei, indent+pi.bound_vars().len()))
            },
            Fix(_, args,_,tp,expr) => {
                args.iter().any(|x| self.is_used_var_aux((*x).1, indent))
                || self.is_used_var_aux(*tp,indent)
                || self.is_used_var_aux(*expr,indent+1+args.len())
            } 
        }
    }

    /// Returns true if the LambdaNode use the variable of
    /// DeBruijn index 0. Doesn't check for uses in Hole types.
    pub fn is_used_var(&self, node: NodeIndex) -> bool {
        self.is_used_var_aux(node, 0)
    }

    // convert a pattern to a string
    fn pattern_to_string_aux(&self, pat:&Pattern, prio:usize) -> String {
        match pat {
            Pattern::Var(x) | Pattern::Const(x) | Pattern::Inductive(x) => var_to_string(&x),
            Pattern::Constr(c,i) => var_to_string(&self.inductives[&i].constructors[*c].0),
            Pattern::App(a,b) if prio == 0 => format!("{} {}",self.pattern_to_string_aux(a,1),self.pattern_to_string_aux(b,0)),
            Pattern::App(..) => format!("({})",self.pattern_to_string_aux(pat,0))
        }
    }
    /// take a patterns and convert it to a String
    pub fn pattern_to_string(&self, pat:&Pattern) -> String {
        self.pattern_to_string_aux(pat,0)
    }

    /// takes a term by NodeIndex and prints it
    /// ``context`` contain the names of the free variable of the term
    fn lambda_to_string_aux(
        &self,
        term: NodeIndex,
        indent: usize,
        prio: usize,
        context: &mut VariablesContext,
    ) -> String {
        use LambdaNode::*;
        match match self.lambda_storage.get(term) {
            None => return "<<INVALID LAMBDA>>".to_owned(),
            Some(e) => e,
        } {
            Var(x) if context.len() > *x => {
                var_to_string(&context.get(context.len() - x - 1).unwrap().0)
            }
            Var(x) if indent > *x => {
                let var: VariableName = ("var".to_string(), indent - x - 1);
                format!("{}", var_to_string(&var))
            }
            Var(x) => {
                format!("<free_var_{}>", *x)
            }
            Const(s) => var_to_string(&s.clone()),
            Pi(var_name, a, b) if prio <= 10 && self.is_used_var(*b) => {
                let ty = self.lambda_to_string_aux(*a, indent, 0, context);
                context.push((var_name.clone(), *a));
                let body = self.lambda_to_string_aux(*b, indent + 1, 10, context);
                context.pop();
                format!(
                    "∀ ({}:{}), {}",
                    var_to_string(&var_name),
                    ty,
                    body
                )
            }
            Pi(var_name, a, b) if prio <= 20 && !self.is_used_var(*b) => {
                let ty = self.lambda_to_string_aux(*a, indent, 21, context);
                context.push((var_name.clone(), *a));
                let body = self.lambda_to_string_aux(*b, indent + 1, 20, context);
                context.pop();
                format!(
                    "{} -> {}",
                    ty,
                    body
                )
            }
            Lam(var_name, a, b) if prio <= 60 => {
                let ty = self.lambda_to_string_aux(*a, indent, 0, context);
                context.push((var_name.clone(), *a));
                let body = self.lambda_to_string_aux(*b, indent + 1, 60, context);
                context.pop();
                format!(
                    "fun ({}:{}) => {}",
                    var_to_string(&var_name),
                    ty,
                    body
                )
            }
            Let(var_name, a, b, c) if prio <= 70 => {
                let ty = self.lambda_to_string_aux(*a, indent, 0, context);
                let e1 = self.lambda_to_string_aux(*b, indent, 70, context);
                context.push((var_name.clone(), *a));
                let e2 = self.lambda_to_string_aux(*c, indent + 1, 70, context);
                context.pop();
                format!(
                    "let ({}:{}) = {} in {}",
                    var_to_string(&var_name),
                    ty,
                    e1,
                    e2
                )
            }
            App(a, b) if prio <= 80 => format!(
                "{} {}",
                self.lambda_to_string_aux(*a, indent, 80, context),
                self.lambda_to_string_aux(*b, indent, 81, context)
            ),
            Prop => format!("Prop"),
            Type(i) if *i == 0 => format!("Set"),
            Type(i) => format!("Type({i})"),

            Hole => format!("<Hole>"), // Hole for a proof
            Inductive(name) => var_to_string(name),
            Constr(n, ind_name, _) => var_to_string(&self.inductives[&ind_name].constructors[*n].0),
            Match(t, x, p, r, v) if prio < 60 => {
                let e1 = self.lambda_to_string_aux(*t, indent, 61, context);
                let name = var_to_string(&x);
                let mut p_vars = p.bound_vars().into_iter().map(|name| (name, term)).collect::<Vec<_>>();
                
                let n_p_vars = p_vars.len();
                context.append(&mut p_vars);
                context.push((x.clone(), *t));
                let e3 = self.lambda_to_string_aux(*r, indent + n_p_vars, 61, context);
                context.pop();
                context.truncate(context.len()-n_p_vars);
                let mut patterns_string = String::new();
                for (pi, ti) in v{
                    let mut pi_vars = pi.bound_vars().into_iter().map(|name| (name, term)).collect::<Vec<_>>();
                    let n_pi_vars = pi_vars.len();
                    context.append(&mut pi_vars);
                    let ei = self.lambda_to_string_aux(*ti, indent + n_pi_vars, 61, context);
                    context.truncate(context.len()-n_pi_vars);

                    patterns_string = format!("{}| {} => {} ", patterns_string, self.pattern_to_string(pi), ei)
                }
                format!("match {} as {} in {} return {} with {}end", e1, name, self.pattern_to_string(p), e3, patterns_string)
            },
            Fix(name,args,stru,tp,expr) if prio < 60 => {
                let args_done = args
                    .iter()
                    .enumerate()
                    .map(|(i,x)| {
                        let res = format!("({}:{})",var_to_string(&x.0),self.lambda_to_string_aux(x.1,indent+i,0,context));
                        context.push((x.0.clone(),x.1));
                        res
                    })
                    .collect::<Vec<String>>()
                    .join(" ");

                let tp_new = self.lambda_to_string_aux(*tp, indent+args.len(), 0, context);
                context.push((name.clone(),*tp));
                
                let f_call = self.lambda_to_string_aux(*expr, indent, 0, context);
                context.truncate(context.len()-1-args.len());

                format!("fix {} {} {{struct {}}} : {} := {}",
                    var_to_string(name),
                    args_done,
                    var_to_string(stru),
                    tp_new,
                    f_call
                )
            }
            Let(..) | Lam(..) | Pi(..) | App(..) | Match(..)| Fix(..) => format!("({})", self.lambda_to_string_aux(term, indent, 0, context)), // match parenthesis
        }
    }

    /// Gives the text representation of the index-th goal 
    pub fn goal_to_string(&self, index: usize) -> String {
        let mut goal: HoleContext = self.goals.get(index).unwrap().clone();
        self.lambda_to_string_aux(goal.goal, 0, 0, &mut goal.context)
    }

    /// gives the string representation of a CLOSED term
    /// if your term may have free variables, use ``lambda_to_string_with_context``
    pub fn lambda_to_string(&self, term: NodeIndex) -> String {
        self.lambda_to_string_aux(term, 0, 0, &mut Vec::new())
    }

    /// returns a string representation of ``term`` (given by ``NodeIndex``)
    /// ``ctx`` contains the variable names of the free variables
    /// although it is borrowed as mutable, its content after the call will be the same as
    /// before the call
    pub fn lambda_to_string_with_context(&self, term: NodeIndex, ctx: &mut VariablesContext) -> String {
        self.lambda_to_string_aux(term, 0, 0, ctx)
    }

    /// Prints a inductive definition 
    pub fn inductive_to_string(&self, name:&VariableName) -> String {
        let data = self.inductives[name].clone();

        let mut gamma = vec![];
        let mut args = vec![];
        for (n,tp) in data.parameters {
            args.push(format!("({}:{})",var_to_string(&n),self.lambda_to_string_with_context(tp,&mut gamma)));
            gamma.push((n,tp))
        }
        let end_tp = self.lambda_to_string_with_context(data.type_of,&mut gamma);
        gamma.push((name.clone(),0));

        let mut constr = vec![];
        for c in data.constructors {
            constr.push(format!("\n | {} : {}",var_to_string(&c.0),self.lambda_to_string_with_context(c.1,&mut gamma)));
        }

        format!("Inductive {} {} : {} := {}",
            var_to_string(name),
            args.join(" "),
            end_tp,
            constr.join("")
        )
    }

}


impl fmt::Display for GlobalContext {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.root {
            None => write!(f, "Not in proof."),
            Some(_) if self.goals.len() == 0 => write!(f, "Proof finished, please use Qed."),
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
                let hypothesis = hypothesis.into_iter().rev().collect::<Vec<String>>().join("\n");

                write!(f, "{}\n{} 1/{}\n{}",
                    hypothesis,
                    "======",
                    self.goals.len(),
                    self.lambda_to_string_with_context(hole_context.goal, context)
                    )
            }
        }
    }
}