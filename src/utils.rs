use std::iter::zip;

use crate::definitions::*;
use crate::errors::*;

/// This file defines utillitaries function about the GlobalCOntext
/// Most of thoses are a way to easly performs operations on LambdaNode, like duplicating a lambdanode, performing an equality etc....


/// A macro to be able to easely insert a LambdaNode while requiring a read-only reference to ctx in $expression
macro_rules! insert {
    ($ctx:expr, $expression:expr) => {{
        let temp = $expression;
        $ctx.insert_node(temp)
    }};
}

// A helper macro that try to get a node and returns an error
macro_rules! get_node {
    ($self:tt, $index:tt) => {
        $self.lambda_storage
            .get($index)
            .cloned()
            .ok_or_else(|| TypingError::NodeIncorrectPointer($index))?
    };
}

impl GlobalContext {
    /// Insert the given node into the `GlobalContext`, and returns the corresponding index.
    pub fn insert_node(&mut self, node: LambdaNode) -> NodeIndex {
        self.lambda_storage.push(node);
        self.lambda_storage.len() - 1
    }

    /// duplicate a node in the memory and return the index of the root of the newly added node
    pub fn deep_copy(&mut self, node: NodeIndex) -> NodeIndex {
        use LambdaNode::*;
        match self.lambda_storage[node].clone() {
            Var(i) => self.insert_node(Var(i)),
            Const(_) | Prop | Type(_) |Hole => node, // no need to copy closed terms
            Lam(var_name, var_t, body) => {
                let var_t = self.deep_copy(var_t);
                let body = self.deep_copy(body);
                self.insert_node(Lam(var_name, var_t, body))
            },
            Pi(var_name, var_t, body) => {
                let var_t = self.deep_copy(var_t);
                let body = self.deep_copy(body);
                self.insert_node(Pi(var_name, var_t, body))
            },
            App(u, v) => {
                let u = self.deep_copy(u);
                let v = self.deep_copy(v);
                self.insert_node(App(u, v))
            }
            Let(var_name, var_t, e1, e2) => {
                let var_t = self.deep_copy(var_t);
                let e1 = self.deep_copy(e1);
                let e2 = self.deep_copy(e2);
                self.insert_node(Let(var_name, var_t, e1, e2))
            }
            Inductive(name) => {
                self.insert_node(Inductive(name.clone()))
            }
            Constr(n, i, t) => {
                let t1 = self.deep_copy(t);
                self.insert_node(Constr(n, i.clone(),t1))
            }
            Match(t, x, p, r, v) => {
                let t = self.deep_copy(t);
                let x = x.clone();
                let p = p.clone();
                let r = self.deep_copy(r);
                let v = v.iter().map(|(pi, ei)| (pi.clone(), self.deep_copy(*ei))).collect();
                self.insert_node(Match(t, x, p, r, v))
            }
            Fix(name, args, stru, tp, body) => {
                let tp = self.deep_copy(tp);
                let body = self.deep_copy(body);
                let args = args.iter().map(|(n,e)|(n.clone(),self.deep_copy(*e))).collect();

                self.insert_node(Fix(name.clone(),args,stru.clone(),tp,body))
            }
        }
    }

    /// Does a deep copy of `node` such that the top term overwrite the node at position `at` (the others are left untouched)
    /// Useful for unwraping constants "in place" for the beta reduction
    pub fn deep_copy_at(&mut self, node: NodeIndex, at:NodeIndex) {
        let v = self.deep_copy(node);
        self.lambda_storage[at] = self.lambda_storage[v].clone();
    }

    /// checks if 2 lambda terms are structurally equal
    /// this goes through all indirections due to our representation
    /// in particular, 2 LambdaNodes might not be equal
    /// but the corresponding lambda terms might be deep_equal
    /// do note this only works with closed terms!
    pub fn deep_equality(&self, l1: NodeIndex, l2: NodeIndex) -> bool {
        use LambdaNode::*;

        match (&self.lambda_storage[l1], &self.lambda_storage[l2]) {
            (Prop, Prop) => true,
            (Hole, Hole) => l1 == l2, // a holes is present at a unique index
            (Type(i), Type(j)) | (Var(i), Var(j)) => i == j,
            (Const(name), _) => {
                let c = self.constants[&name].0;
                self.deep_equality(c, l2)
            },
            (_, Const(name)) => {
                let c = self.constants[&name].0;
                self.deep_equality(l1, c)
            },
            (Pi(_, x1, y1), Pi(_, x2, y2))
            | (Lam(_, x1, y1), Lam(_, x2, y2))
            | (App(x1, y1), App(x2, y2)) => {
                self.deep_equality(*x1, *x2) && self.deep_equality(*y1, *y2)
            }
            (Let(v1, x1, y1, z1), Let(v2, x2, y2, z2)) => {
                self.deep_equality(*x1, *x2)
                    && self.deep_equality(*y1, *y2)
                    && self.deep_equality(*z1, *z2)
                    && v1 == v2
            }
            (Match(t1, _, p1, r1, v1), Match(t2, _, p2, r2, v2)) => {
                self.deep_equality(*t1, *t2)
                && p1 == p2
                && self.deep_equality(*r1, *r2)
                && zip(v1, v2).all(|((pi1, ei1), (pi2, ei2))| {
                    pi1 == pi2 && self.deep_equality(*ei1, *ei2)
                })
            }
            (Inductive(n1), Inductive(n2)) => n1 == n2,
            (Constr(i1, ind1, t1), Constr(i2, ind2, t2)) => {
                i1 == i2 && ind1 == ind2 && self.deep_equality(*t1, *t2)
            }
            (Fix(n1, a1, s1, tp1, expr1),Fix(n2, a2, s2, tp2, expr2)) => {
                self.deep_equality(*expr1, *expr2) &&
                self.deep_equality(*tp1, *tp2) &&
                n1 == n2 &&
                s1 == s2 &&
                zip(a1,a2).all(|((an1,aexpr1),(an2,aexpr2))| an1 == an2 && self.deep_equality(*aexpr1,*aexpr2))
            },
            (Prop, _) | (Hole, _) | (Type(_), _) | (Var(_), _) | (Pi(..), _) | (Lam(..), _) | (Fix(..), _) | (App(..), _) | (Let(..), _) | (Match(..), _) | (Inductive(_), _) | (Constr(..), _)/* No wildcard for futur-proofing */  => false,
        }
    }

    /// computes deep equality of terms with potential free variables
    /// i.e. it takes the context in which both terms should be interpreted
    /// it will check that free variables correspond to the same in both terms
    /// even though their DeBruijn indices may differ
    /// it assumes that both terms were defined with a common ground context
    /// but that they were defined at a different time
    pub fn deep_equality_with_contexts(
        &self,
        gamma1: &mut TypingContext,
        l1: NodeIndex,
        gamma2: &mut TypingContext,
        l2: NodeIndex,
    ) -> Result<bool, TypingError> {
        use LambdaNode::*;
        let otp = match (get_node!(self, l1), get_node!(self, l2)) {
            (Var(i), Var(j)) => i + gamma2.len() == j + gamma1.len(),
            (Prop, Prop) => true,
            (Hole, Hole) => l1 == l2, // a holes is present at a unique index
            (Type(i), Type(j)) => i == j,
            (Const(name), _) => {
                let c = self.constants[&name].0;
                self.deep_equality_with_contexts(gamma1, c, gamma2, l2)?
            },
            (_, Const(name)) => {
                let c = self.constants[&name].0;
                self.deep_equality_with_contexts(gamma1, l1, gamma2, c)?
            },
            (Pi(v1, x1, y1), Pi(v2, x2, y2))
            | (Lam(v1, x1, y1), Lam(v2, x2, y2)) => {
                let temp = self.deep_equality_with_contexts(gamma1, x1, gamma2, x2)?;
                gamma1.push((v1, x1)); gamma2.push((v2, x2));
                let temp1 = self.deep_equality_with_contexts(gamma1, y1, gamma2, y2);
                gamma1.pop(); gamma2.pop();
                temp1? && temp

            }
            (App(x1, y1), App(x2, y2)) => {
                self.deep_equality_with_contexts(gamma1, x1, gamma2, x2)?
                && self.deep_equality_with_contexts(gamma1, y1, gamma2, y2)?
            }
            (Let(v1, x1, y1, z1), Let(v2, x2, y2, z2)) => {
                self.deep_equality(x1, x2)
                    && self.deep_equality(y1, y2)
                    && self.deep_equality(z1, z2)
                    && v1 == v2
            }
            (Inductive(name1), Inductive(name2)) => name1 == name2,
            (Constr(i1, ind_name1, _), Constr(i2, ind_name2, _)) => i1 == i2 && ind_name1 == ind_name2,
            (Match(t1, x1, p1, r1, v1), Match(t2, x2, p2, r2, v2)) => {
                if !self.deep_equality_with_contexts(gamma1, t1, gamma2, t2)? || x1 != x2 || p1 != p2 {return Ok(false)}
                p1.bound_vars().into_iter().for_each(|name| gamma1.push((name, 0)));
                p2.bound_vars().into_iter().for_each(|name| gamma2.push((name, 0)));
                let _r1_eq_r2 = self.deep_equality_with_contexts(gamma1, r1, gamma2, r2);
                gamma1.truncate(gamma1.len()-p1.bound_vars().len());
                gamma2.truncate(gamma1.len()-p2.bound_vars().len());
                if v1.len() != v2.len() {return Ok(false)};
                for ((pi1, ei1), (pi2, ei2)) in zip(v1, v2) {
                    if pi1 != pi2 {return Ok(false)}
                    pi1.bound_vars().into_iter().for_each(|name| gamma1.push((name, 0)));
                    pi2.bound_vars().into_iter().for_each(|name| gamma2.push((name, 0)));
                    let _ei1_eq_ei2 = self.deep_equality_with_contexts(gamma1, ei1, gamma2, ei2);
                    gamma1.truncate(gamma1.len()-pi1.bound_vars().len());
                    gamma2.truncate(gamma2.len()-pi2.bound_vars().len());
                }
                true
            },
            (Fix(n1, a1, s1, tp1, expr1),Fix(n2, a2, s2, tp2, expr2)) => {
                if !self.deep_equality_with_contexts(gamma1, expr1, gamma2, expr2)? ||
                !self.deep_equality_with_contexts(gamma1, tp1, gamma2, tp2)? ||
                n1 != n2 || s1 != s2 {return Ok(false)}
                for ((an1, aexpr1), (an2, aexpr2)) in zip(a1, a2) {
                    if an1 != an2 || !self.deep_equality_with_contexts(gamma1, aexpr1, gamma2, aexpr2)? {return Ok(false)}
                }
                true
            },
            _ => false,
        };
        Ok(otp)
    }

    /// auxiliary function for shift_index
    /// it ensures we do not shift indices that are too local 
    pub fn shift_index_aux(&mut self, amount: isize, lambda: NodeIndex, threshold: usize) -> LambdaNode {
        use LambdaNode::*;

        match &self.lambda_storage[lambda].clone() {
            Var(i) => {
                if *i >= threshold {
                    Var(i.wrapping_add_signed(amount))
                } else {
                    Var(*i)
                }
            }
            Const(c) => Const(c.clone()),
            Prop => Prop,
            Type(i) => Type(*i),
            Pi(var_name, t, l) => {
                let var_name = var_name.clone();
                let l2 = *l;
                let t2 = *t;
                let t = insert!(self, self.shift_index_aux(amount, t2, threshold));
                let l = insert!(self, self.shift_index_aux(amount, l2, threshold + 1));
                Pi(var_name, t, l)
            }
            Lam(var_name, t, l) => {
                let var_name = var_name.clone();
                let l2 = *l;
                let t2 = *t;
                let t = insert!(self, self.shift_index_aux(amount, t2, threshold));
                let l = insert!(self, self.shift_index_aux(amount, l2, threshold + 1));
                Lam(var_name, t, l)
            }
            App(l, t) => {
                let l2 = *l;
                let t2 = *t;
                let l1 = insert!(self, self.shift_index_aux(amount, l2, threshold));
                let l2 = insert!(self, self.shift_index_aux(amount, t2, threshold));
                App(l1, l2)
            }
            Let(var_name, t, v, l) => {
                let var_name = var_name.clone();
                let t2 = *t;
                let v2 = *v;
                let l2 = *l;
                let t = insert!(self, self.shift_index_aux(amount, t2, threshold));
                let v = insert!(self, self.shift_index_aux(amount, v2, threshold));
                let l = insert!(self, self.shift_index_aux(amount, l2, threshold + 1));
                Let(var_name, t, v, l)
            }
            Hole => Hole,
            Inductive(name) => Inductive(name.clone()),
            Constr(n, ind, t) => {
                let n = *n;
                let ind = ind.clone();
                let t2 = *t;
                let t = insert!(self, self.shift_index_aux(amount, t2, threshold));
                Constr(n, ind, t) 
            }
            Match(t, x, p, r, v) => {
                let t = *t;
                let x = x.clone();
                let p = p.clone();
                let r = *r;
                let v = v.clone();
                let t = insert!(self, self.shift_index_aux(amount, t, threshold));
                let r = insert!(self, self.shift_index_aux(amount, r, threshold+p.bound_vars().len()+1));
                let mut v1 = Vec::new();
                for (pi, ei) in v {
                    v1.push((pi.clone(), insert!(self, self.shift_index_aux(amount, ei, threshold+pi.bound_vars().len()))))
                }
                Match(t, x.clone(), p.clone(), r, v1)
            }
            Fix(name, args, decreasing, t, body) => {
                let mut threshold = threshold;
                let mut new_args = Vec::new();
                for (n, ti) in args.iter(){
                    let ti = insert!(self, self.shift_index_aux(amount, *ti, threshold));
                    threshold += 1;
                    new_args.push((n.clone(), ti));
                }
                let t = insert!(self, self.shift_index_aux(amount, *t, threshold));
                threshold += 1;
                let body = insert!(self, self.shift_index_aux(amount, *body, threshold));
                Fix(name.clone(), new_args, decreasing.clone(), t, body)
            }
        }
    }

    /// Return the lambda-term obtained after shifting every De Bruijn Index by `amount`.
    pub fn shift_index(&mut self, amount: isize, lambda: NodeIndex) -> LambdaNode {
        self.shift_index_aux(amount, lambda, 0)
    }

    /// Returns the NodeIndex of lambda-term obtained after shifting every
    /// De Bruijn Index by `amount` in `lambda`, provided their index is already >= threshold
    /// It keeps the old lambdaTerm around
    pub fn shift_index_keep(
        &mut self,
        amount: usize,
        threshold: usize,
        lambda: NodeIndex,
    ) -> NodeIndex {
        use LambdaNode::*;
        if amount == 0 {
            return lambda;
        }
        match &self.lambda_storage[lambda].clone() {
            Var(i) => {
                if *i >= threshold {
                    self.insert_node(Var(i + amount))
                } else {
                    lambda
                }
            }
            Const(_) => lambda,
            Prop => self.insert_node(Prop),
            Type(i) => self.insert_node(Type(*i)),
            Pi(var_name, t, l) => {
                let var_name = var_name.clone();
                let t = self.shift_index_keep(amount, threshold, *t);
                let l = self.shift_index_keep(amount, threshold + 1, *l);
                self.insert_node(Pi(var_name, t, l))
            }
            Lam(var_name, t, l) => {
                let var_name = var_name.clone();
                let t = self.shift_index_keep(amount, threshold, *t);
                let l = self.shift_index_keep(amount, threshold + 1, *l);
                self.insert_node(Lam(var_name, t, l))
            }
            App(l, t) => {
                let l = self.shift_index_keep(amount, threshold, *l);
                let t = self.shift_index_keep(amount, threshold, *t);
                self.insert_node(App(l, t))
            }
            Let(var_name, t, v, l) => {
                let var_name = var_name.clone();
                let t = self.shift_index_keep(amount, threshold, *t);
                let v = self.shift_index_keep(amount, threshold, *v);
                let l = self.shift_index_keep(amount, threshold + 1, *l);
                self.insert_node(Let(var_name, t, v, l))
            }
            Hole => panic!("Trying to apply index shift to a lambda-term containing a hole."),
            Inductive(name) => {
                self.insert_node(Inductive(name.clone()))
            }
            Constr(n, i, t) => {
                let t = self.shift_index_keep(amount, threshold, *t);
                self.insert_node(Constr(*n, i.clone(), t))
            }
            Match(t, x, p, r, v) => {
                let t = self.shift_index_keep(amount, threshold, *t);
                let x = x.clone();
                let r = self.shift_index_keep(amount, threshold+p.bound_vars().len()+1, *r);
                let p = p.clone();
                let v = v
                    .iter()
                    .map(|(pi, ei)|
                        (pi.clone(), self.shift_index_keep(amount, threshold+pi.bound_vars().len(), *ei))
                    ).collect();
                self.insert_node(Match(t, x, p, r, v))
            }
            Fix(name,args,stru,tp,expr) => {

                let args_new = args
                    .iter()
                    .enumerate()
                    .map(|(i,(xname,xv))| (xname.clone(), self.shift_index_keep(amount, threshold+i, *xv)))
                    .collect::<Vec<(VariableName,NodeIndex)>>();
                let tp_new = self.shift_index_keep(amount, threshold+args_new.len(), *tp);
                let expr_new = self.shift_index_keep(amount, threshold+1+args_new.len(), *expr);

                self.insert_node(Fix(name.clone(), args_new, stru.clone(), tp_new, expr_new))
            }
        }
    }

    /// Replace every occurence of constant `name` in `lamb` by a copy of `cst` in place. Will overwrite the lambda.
    pub fn replace_const(
        &mut self,
        lambda: NodeIndex,
        name: &VariableName,
        cst: NodeIndex,
    ) -> Result<(),Error> {
        use LambdaNode::*;
        match &self.lambda_storage[lambda].clone() {
            Const(n) if name == n => {
                let v = self.deep_copy(cst);
                self.lambda_storage[lambda] = self.lambda_storage[v].clone();
                Ok(())
            },
            Inductive(_) | Var(_) | Prop | Type(_) | Const(_) => Ok(()),
            Pi(v, t, _) | Lam(v, t, _) if v == name => {
                self.replace_const(*t, name, cst)
            },
            Pi(_, t, l) | Lam(_, t, l) | App(t, l) => {
                self.replace_const(*t, name, cst)?;
                self.replace_const(*l, name, cst)
            },
            Let(v, t, l, _) if v == name => {
                self.replace_const(*t, name, cst)?;
                self.replace_const(*l, name, cst)
            },
            Let(_, t, l, e) => {
                self.replace_const(*t, name, cst)?;
                self.replace_const(*e, name, cst)?;
                self.replace_const(*l, name, cst)
            }
            Hole => Err(InternalError::HoleContained("GlobalContext::replace_const").into()),
            Constr(_, _, t) => self.replace_const(*t, name, cst),
            Match(t, _, _, r, v) => {
                self.replace_const(*t, name, cst)?;
                self.replace_const(*r, name, cst)?;
                for (_, ei) in v {
                    self.replace_const(*ei, name, cst)?;
                }
                Ok(())
            }
            Fix(_,args,_,tp,expr) => {
                self.replace_const(*expr, name, cst)?;
                self.replace_const(*tp, name, cst)?;
                for (_, ei) in args {
                    self.replace_const(*ei, name, cst)?;
                }
                Ok(())
            }
        }
    }

    /// replaces the variable of Debruijn index depth in the term lambda
    /// with the term value
    /// in contrast with ``replace_depth``, it keeps the old terms intact
    /// (and at the same place)
    pub fn brute_replace_depth_keep(
        &mut self,
        lambda: NodeIndex,
        value: NodeIndex,
        depth: usize,
    ) -> NodeIndex {
        use LambdaNode::*;
        match &self.lambda_storage[lambda].clone() {
            Var(i) => {
                if *i == depth {
                    self.deep_copy(value)
                } else if *i > depth {
                    self.insert_node(Var(*i-1))
                }else {
                    self.insert_node(Var(*i))
                }
            }
            Const(_) | Prop | Type(_) => lambda,
            Pi(var_name, t, l) => {
                let var_name = var_name.clone();
                let t = self.replace_depth_keep(*t, value, depth);
                let l = self.replace_depth_keep(*l, value, depth + 1);
                self.insert_node(Pi(var_name, t, l))
            }
            Lam(var_name, t, l) => {
                let var_name = var_name.clone();
                let t = self.replace_depth_keep(*t, value, depth);
                let l = self.replace_depth_keep(*l, value, depth + 1);
                self.insert_node(Lam(var_name, t, l))
            }
            App(l1, l2) => {
                let l1 = self.replace_depth_keep(*l1, value, depth);
                let l2 = self.replace_depth_keep(*l2, value, depth);
                self.insert_node(App(l1, l2))
            }
            Let(var_name, t, v, l) => {
                let var_name = var_name.clone();
                let t = self.replace_depth_keep(*t, value, depth);
                let v = self.replace_depth_keep(*v, value, depth);
                let l = self.replace_depth_keep(*l, value, depth + 1);
                self.insert_node(Let(var_name, t, v, l))
            }
            Hole => panic!("Trying to replace variable in a lambda term containing a hole."),
            Inductive(name) => {
                self.insert_node(Inductive(name.clone()))
            }
            Constr(n, i, t) => {
                let t = self.replace_depth_keep(*t, value, depth);
                self.insert_node(Constr(*n, i.clone(), t))
            }
            Match(t, x, p, r, v) => {
                let t = self.replace_depth_keep(*t, value, depth);
                let x = x.clone();
                let p = p.clone();
                let r = self.replace_depth_keep(*r, value, depth+p.bound_vars().len()+1);
                let v = v
                    .iter()
                    .map(|(pi, ei)| (pi.clone(), self.replace_depth_keep(*ei, value, depth+pi.bound_vars().len())))
                    .collect();
                self.insert_node(Match(t, x, p, r, v))
            }
            Fix(name,args,stru,tp,expr) => {
                let name = name.clone();
                let stru = stru.clone();
                let args = args
                    .iter()
                    .enumerate()
                    .map(|(i,(xname,xv))| (xname.clone(), self.replace_depth_keep(*xv, value, depth+i)))
                    .collect::<Vec<(VariableName,NodeIndex)>>();
                let tp = self.replace_depth_keep(*tp, value, depth + args.len());
                let expr = self.replace_depth_keep(*expr, value, depth + 1 + args.len());
                self.insert_node(Fix(name,args,stru,tp,expr))
            }
        }
    }

    /// replaces the variable at depth ``depth`` in lambda with the value ``value``
    fn replace_depth(&mut self, lambda: NodeIndex, value: NodeIndex, depth: usize) -> LambdaNode {
        use LambdaNode::*;
        let x = &self.lambda_storage[lambda].clone();
        match x {
            Var(i) => {
                if *i == depth {
                    self.shift_index(depth as isize, value)
                } else if *i > depth {
                    Var(*i - 1)
                } else {
                    Var(*i)
                }
            }
            Const(c) => Const(c.clone()),
            Prop => Prop,
            Type(i) => Type(*i),
            Pi(var_name, t, l) => {
                let var_name = var_name.clone();
                let l2 = *l;
                let t2 = *t;
                let t = insert!(self, self.replace_depth(t2, value, depth));
                let l = insert!(self, self.replace_depth(l2, value, depth + 1));
                Pi(var_name, t, l)
            }
            Lam(var_name, t, l) => {
                let var_name = var_name.clone();
                let l2 = *l;
                let t2 = *t;
                let t = insert!(self, self.replace_depth(t2, value, depth));
                let l = insert!(self, self.replace_depth(l2, value, depth + 1));
                Lam(var_name, t, l)
            }
            App(l1, l2) => {
                let l1b = *l1;
                let l2b = *l2;
                let l1 = insert!(self, self.replace_depth(l1b, value, depth));
                let l2 = insert!(self, self.replace_depth(l2b, value, depth));
                App(l1, l2)
            }
            Let(var_name, t, v, l) => {
                let var_name = var_name.clone();
                let t2 = *t;
                let v2 = *v;
                let l2 = *l;
                let t = insert!(self, self.replace_depth(t2, value, depth));
                let v = insert!(self, self.replace_depth(v2, value, depth));
                let l = insert!(self, self.replace_depth(l2, value, depth + 1));
                Let(var_name, t, v, l)
            }
            Hole => panic!("Trying to replace variable in a lambda term containing a hole."),
            Inductive(name) => Inductive(name.clone()),
            Constr(n, ind, t) => {
                let n = *n;
                let ind = ind.clone();
                let t2 = *t;
                let t = insert!(self, self.replace_depth(t2, value, depth));
                Constr(n, ind, t)
            }
            Match(t, x, p, r, v) => {
                let t = *t;
                let x = x.clone();
                let p = p.clone();
                let r = *r;
                let v = v.clone();
                let t = insert!(self, self.replace_depth(t, value, depth));
                let r = insert!(self, self.replace_depth(r, value, depth+p.bound_vars().len()+1));
                let mut v1 = Vec::new();
                for (pi, ei) in v {
                    v1.push((pi.clone(), insert!(self, self.replace_depth(ei, value, depth+pi.bound_vars().len()))))
                }
                Match(t, x.clone(), p.clone(), r, v1)
            }
            Fix(name, args, decreasing, t, body) => {
                let mut depth = depth;
                let mut new_args = Vec::new();
                for (n, ti) in args.iter(){
                    let ti = insert!(self, self.replace_depth(*ti, value, depth));
                    depth += 1;
                    new_args.push((n.clone(), ti));
                }
                let t = insert!(self, self.replace_depth(*t, value, depth));
                depth += 1;
                let body = insert!(self, self.replace_depth(*body, value, depth));
                Fix(name.clone(), new_args, decreasing.clone(), t, body)
            }
        }
    }

    /// Return the lambda-term obtained after replacing variable with De Bruijn index 0
    /// by the lambda term `value`.
    pub fn replace(&mut self, lambda: NodeIndex, value: NodeIndex) -> LambdaNode {
        self.replace_depth(lambda, value, 0)
    }

    /// replaces the variable of Debruijn index depth in the term lambda
    /// with the term value
    /// in contrast with ``replace_depth``, it keeps the old terms intact
    /// (and at the same place)
    pub fn replace_depth_keep(
        &mut self,
        lambda: NodeIndex,
        value: NodeIndex,
        depth: usize,
    ) -> NodeIndex {
        use LambdaNode::*;
        match &self.lambda_storage[lambda].clone() {
            Var(i) => {
                if *i == depth {
                    self.shift_index_keep(depth, 0, value)
                } else if *i > depth {
                    self.insert_node(Var(*i-1))
                }else {
                    self.insert_node(Var(*i))
                }
            }
            Const(_) | Prop | Type(_) => lambda,
            Pi(var_name, t, l) => {
                let var_name = var_name.clone();
                let t = self.replace_depth_keep(*t, value, depth);
                let l = self.replace_depth_keep(*l, value, depth + 1);
                self.insert_node(Pi(var_name, t, l))
            }
            Lam(var_name, t, l) => {
                let var_name = var_name.clone();
                let t = self.replace_depth_keep(*t, value, depth);
                let l = self.replace_depth_keep(*l, value, depth + 1);
                self.insert_node(Lam(var_name, t, l))
            }
            App(l1, l2) => {
                let l1 = self.replace_depth_keep(*l1, value, depth);
                let l2 = self.replace_depth_keep(*l2, value, depth);
                self.insert_node(App(l1, l2))
            }
            Let(var_name, t, v, l) => {
                let var_name = var_name.clone();
                let t = self.replace_depth_keep(*t, value, depth);
                let v = self.replace_depth_keep(*v, value, depth);
                let l = self.replace_depth_keep(*l, value, depth + 1);
                self.insert_node(Let(var_name, t, v, l))
            }
            Hole => panic!("Trying to replace variable in a lambda term containing a hole."),
            Inductive(name) => {
                self.insert_node(Inductive(name.clone()))
            }
            Constr(n, i, t) => {
                let t = self.replace_depth_keep(*t, value, depth);
                self.insert_node(Constr(*n, i.clone(), t))
            }
            Match(t, x, p, r, v) => {
                let t = self.replace_depth_keep(*t, value, depth);
                let x = x.clone();
                let p = p.clone();
                let r = self.replace_depth_keep(*r, value, depth+p.bound_vars().len()+1);
                let v = v
                    .iter()
                    .map(|(pi, ei)| (pi.clone(), self.replace_depth_keep(*ei, value, depth+pi.bound_vars().len())))
                    .collect();
                self.insert_node(Match(t, x, p, r, v))
            }
            Fix(name,args,stru,tp,expr) => {
                let name = name.clone();
                let stru = stru.clone();
                let args = args
                    .iter()
                    .enumerate()
                    .map(|(i,(xname,xv))| (xname.clone(), self.replace_depth_keep(*xv, value, depth+i)))
                    .collect::<Vec<(VariableName,NodeIndex)>>();
                let tp = self.replace_depth_keep(*tp, value, depth + args.len());
                let expr = self.replace_depth_keep(*expr, value, depth + 1 + args.len());
                self.insert_node(Fix(name,args,stru,tp,expr))
            }
        }
    }

    /// replaces the value of Debruijn index 0 in lambda with value
    /// in contrast with ``replace`` it keeps the old terms intact (at the same places)
    /// and generates any new needed term
    /// it returns the ``NodeIndex`` where the new term is stored
    pub fn replace_keep(&mut self, lambda: NodeIndex, value: NodeIndex) -> NodeIndex {
        self.replace_depth_keep(lambda, value, 0)
    }

    /// auxiliary function for shift_index
    /// it ensures we do not shift indices that are too local 
    fn shift_index_overwrite_aux(&mut self, amount: isize, lambda: NodeIndex, threshold: usize) {
        use LambdaNode::*;

        match self.lambda_storage[lambda].clone() {
            Var(i) if i >= threshold => self.lambda_storage[lambda] = Var(i.wrapping_add_signed(amount)),
            Inductive(_) | Var(_) | Prop | Type(_) | Const(_) => (), // closed terms
            Pi(_, t, l) => {
                self.shift_index_overwrite_aux(amount, t, threshold);
                self.shift_index_overwrite_aux(amount, l, threshold + 1);
            }
            Lam(_, t, l) => {
                self.shift_index_overwrite_aux(amount, t, threshold);
                self.shift_index_overwrite_aux(amount, l, threshold + 1);
            }
            App(l, t) => {
                self.shift_index_overwrite_aux(amount, l, threshold);
                self.shift_index_overwrite_aux(amount, t, threshold);
            }
            Let(_, t, v, l) => {
                self.shift_index_overwrite_aux(amount, t, threshold);
                self.shift_index_overwrite_aux(amount, v, threshold);
                self.shift_index_overwrite_aux(amount, l, threshold + 1);
            }
            Hole => panic!("Trying to apply index shift to a lambda-term containing a hole."),
            Constr(_, _, t) => self.shift_index_overwrite_aux(amount, t, threshold),
            Match(t, _, p, r, v) => {
                self.shift_index_overwrite_aux(amount, t, threshold);
                self.shift_index_overwrite_aux(amount, r, threshold+p.bound_vars().len()+1);
                v.iter().for_each(|(pi, ei)|
                    self.shift_index_overwrite_aux(amount, *ei, threshold+pi.bound_vars().len())
                )
            }
            Fix(_,args,_,tp,expr) => {
                args.iter().enumerate().for_each(|(i,(_,e))| self.shift_index_overwrite_aux(amount, *e, threshold+i));
                self.shift_index_overwrite_aux(amount, tp, threshold+args.len());
                self.shift_index_overwrite_aux(amount, expr, threshold+1+args.len());
            }
        }
    }
    
    /// Shifts all De Bruijn indices in the term`lambda` by `amount`
    /// It overwrites the data (and must thus be undone properly by shifting -amount)
    pub fn shift_index_overwrite(&mut self, amount: isize, lambda: NodeIndex) {
        self.shift_index_overwrite_aux(amount, lambda, 0)
    }

    /// unfolds the constants contained in the term stored at``node``
    /// we clone the constants definitions
    /// for now it clones the entire term, so, you know, it may be optimized
    pub fn unfold_constants(&mut self, node: NodeIndex) -> Result<NodeIndex, InternalError> {
        use LambdaNode::*;
        match match self.lambda_storage.get(node) {
            None => return Err(InternalError::NodeIncorrectPointer(node)),
            Some(e) => e.clone(),
        } {
            Var(_) => Ok(node),
            Const(name) => {
                let t = self.deep_copy(self.constants[&name].0);
                self.unfold_constants(t)
            }
            Pi(var_name, var_t, body) => {
                let var_t = self.unfold_constants(var_t)?;
                let body = self.unfold_constants(body)?;
                Ok(self.insert_node(Pi(var_name.clone(), var_t, body)))
            },
            Lam(var_name, var_t, body) => {
                let var_t = self.unfold_constants(var_t)?;
                let body = self.unfold_constants(body)?;
                Ok(self.insert_node(Lam(var_name.clone(), var_t, body)))
            },
            App(u, v) => {
                let u = self.unfold_constants(u)?;
                let v = self.unfold_constants(v)?;
                Ok(self.insert_node(App(u, v)))
            },
            Let(var_name, var_t, e1, e2) => {
                let var_t = self.unfold_constants(var_t)?;
                let e1 = self.unfold_constants(e1)?;
                let e2 = self.unfold_constants(e2)?;
                Ok(self.insert_node(Let(var_name.clone(), var_t, e1, e2)))
            }
            Prop => Ok(node),
            Type(_) => Ok(node),
            Hole => Ok(node),
            Inductive(name) => {
                Ok(self.insert_node(Inductive(name.clone())))
            }
            Constr(n, i, t) => {
                let t = self.unfold_constants(t)?;
                Ok(self.insert_node(Constr(n, i.clone(), t)))
            }
            Match(t, x, p, r, v) => {
                let t = self.unfold_constants(t)?;
                let mut v1 = Vec::new();
                for (pi, ei) in v .into_iter() {
                    v1.push((pi, self.unfold_constants(ei)?))
                }
                Ok(self.insert_node(Match(t, x, p, r, v1)))
            }
            Fix(name,args,stru,tp,body) => {
                let tp = self.unfold_constants(tp)?;
                let body = self.unfold_constants(body)?;
                let mut args_new = Vec::new();
                for (pi, ei) in args.into_iter() {
                    args_new.push((pi.clone(), self.unfold_constants(ei)?))
                }
                Ok(self.insert_node(Fix(name.clone(), args_new, stru.clone(), tp, body)))

            }
        }
    }

    /// replaces all variable names in a pattern by the associated
    /// constructor, inductive or const
    /// if they actually corresponded to constructors
    pub fn clean_pattern(&self, p:Pattern) -> Pattern {
        use Pattern::*;
        match p {
            Var(ref name) => {
                if let Some(_) = self.constants.get(&name) {
                    Const(name.clone())
                } else if let Some(_) = self.inductives.get(&name) {
                    Inductive(name.clone())
                } else if let Some((i, type_name, _)) = self.is_cons(name) {
                    Constr(i, type_name)
                } else {
                    p
                }
            },
            App(p1, p2) => {
                let p1 = self.clean_pattern(*p1);
                let p2 = self.clean_pattern(*p2);
                App(Box::new(p1), Box::new(p2))
            }
            Constr(_, _) | Const(_) | Inductive(_) => p
        }
    }

    /// checks if the given name is currently a constructor name
    /// if so, it returns the index of the constructor, along with the name of the
    /// inductive and its type
    pub fn is_cons(&self, name:&VariableName) -> Option<(usize, VariableName, NodeIndex)> {
        self.inductives.iter().find_map(|(ind_name, ind_data)| 
            ind_data.constructors.iter()
                .enumerate()
                .find(|(_, (cons_name, _))| cons_name == name)
                .map(|(i, (_, ty))| (i, ind_name.clone(), *ty))
        )
    }

    fn pattern_match_aux(&self, t:NodeIndex, p:&Pattern, mut acc: Vec<NodeIndex>) -> Option<Vec<NodeIndex>> {
        use Pattern::*;
        match (p, self.lambda_storage[t].clone()) {
            (Var(v), _) if *v != (String::from(""), 0) => {
                acc.push(t);
                Some(acc)
            },
            (Var(_), _) => Some(acc),
            (Constr(i_p, type_name_p), LambdaNode::Constr(i_t, type_name_t, _))
                if *i_p == i_t && *type_name_p == type_name_t => Some(acc),
            (App(p1, p2), LambdaNode::App(t1, t2)) => {
                let acc = self.pattern_match_aux(t1, p1.as_ref(), acc)?;
                self.pattern_match_aux(t2, p2.as_ref(), acc)
            },
            _ => None

        }
    }

    /// tries to match a term t against a pattern p
    /// it returns the vector of matched terms
    /// the order is deterministic with regard to the pattern
    /// it is the order in which variables are seen
    pub fn pattern_match(&self, t:NodeIndex, p: &Pattern) -> Option<Vec<NodeIndex>> {
        self.pattern_match_aux(t, p, Vec::new())
    }

    /// goes through the needed constants or Inductive indirection
    pub fn get_real(&mut self, t:NodeIndex) -> NodeIndex {
        use LambdaNode::*;
        match self.lambda_storage[t].clone() {
            Const(name) => self.get_real(self.constants[&name].0),
            Inductive(name) => {
                let mut t = self.inductives[&name].type_of;
                for (var_name, var_ty) in self.inductives[&name].parameters.clone() {
                    t = self.insert_node(Pi(var_name, var_ty, t))
                }
                t
            }
            Var(..) | Lam(..) | Pi(..) | App(..) | Let(..) | Prop | Type(..) | Hole |
            Match(..) | Constr(..) | Fix(..) => t,
        }
    }

}



