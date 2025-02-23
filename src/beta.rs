use core::panic;

use crate::definitions::*;

/// This file contains functions about beta reduction and how to calcule the beta normal form of a LambdaNode

#[allow(dead_code, unused_variables)]
impl GlobalContext {
    // Given a lambda of the form `(fix ...) A1 ... AN`, return Some((N, the position of fix))
    fn find_fixpoint_application(&self, lambda: NodeIndex) -> Option<(usize, NodeIndex)>{
        match self.lambda_storage[lambda].clone(){
            LambdaNode::Fix(..) => Some((0, lambda)),
            LambdaNode::App(lhs, ..) => self.find_fixpoint_application(lhs).map(|(n, node)| (n+1, node)),
            _ => None,   
        }
    }

    // Test wether a lambda is of the form Constr A1 ... AN
    fn is_constructor_application(&mut self, lambda: NodeIndex) -> bool{
        if let LambdaNode::Const(name) = self.lambda_storage[lambda].clone() { // unwrap the constantss
            self.deep_copy_at(self.constants[&name].0,lambda);
        };
        match self.lambda_storage[lambda].clone(){
            | LambdaNode::App(lhs, _) => self.is_constructor_application(lhs),
            | LambdaNode::Constr(_, _, _) => true,
            _ => false
        }
    }

    // Take a lambda and reduce it in place if it's a *reducible* fixpoint application, i.e. of the form `(fix ...) A1 ... AN`
    // Returns wherever it suceeded in reducing it or not (and so wheter or not it need a new beta_reduction pass)
    fn reduce_fixpoint(&mut self, lambda: NodeIndex) -> bool {
        // Test it's a fix application
        if let Some((depth, fixpoint)) = self.find_fixpoint_application(lambda){
            if let LambdaNode::Fix(name, args, decreasing_arg, t, body) = self.lambda_storage[fixpoint].clone(){ //this condition necessarily exists
                // Gets the 'struct' argument
                let mut decreasing_arg_pos = None;
                for (i, (n, _)) in args.iter().enumerate(){
                    if n == &decreasing_arg{
                        decreasing_arg_pos = Some(i);
                    }
                }

                if let Some(decreasing_arg_pos) = decreasing_arg_pos {
                    if depth == args.len(){ //we should check whether the decreasing argument is a constructor
                        let mut decreasing_arg_depth = depth-decreasing_arg_pos-1;
                        let mut actual = lambda;
                        while decreasing_arg_depth > 0 {
                            match self.lambda_storage[actual].clone(){
                                LambdaNode::App(lhs, _) => {
                                    actual = lhs;
                                    decreasing_arg_depth-=1;
                                }
                                _ => panic!("Couldn't find the decreasing argument.")
                            }
                        }

                        // if the struct argument is decreasing, reduce
                        if let LambdaNode::App(_, rhs) = self.lambda_storage[actual].clone(){
                            if self.is_constructor_application(rhs){ // we need to beta-reduce the fixpoint application
                                let mut actual = self.replace(body, fixpoint);
                                for (name, t) in args.iter().rev(){
                                    actual = LambdaNode::Lam(name.clone(), self.deep_copy(*t), self.insert_node(actual)); // Trasnform it in a serie of lambda
                                }
                                self.lambda_storage[fixpoint] = actual;
                                return true;
                            }
                        }
                    }
                }
            }
        }
        return false;
    }

    /// Calculate the beta-normal form of a lambda node *in place*
    /// It will unwrap constants when necesarry (for example when `const arg` it will unwrap const to be able to reduce it)
    pub fn beta_reduction(&mut self, lambda: NodeIndex) {
        use LambdaNode::*;
        match self.lambda_storage[lambda].clone() {
            Var(_) | Prop | Type(_) => (),
            Inductive(_) | Const(..) => (), // We do not reduce Const or Inductive here
            Pi(_, l1, l2) | Lam(_, l1, l2) => {
                self.beta_reduction(l1);
                self.beta_reduction(l2);
            }
            Let(_, _, v, l) => {
                // We do not beta reduce the type since it is discarded after reduction of let
                self.beta_reduction(v);
                self.beta_reduction(l);
                self.lambda_storage[lambda] = self.replace(l, v);
                self.beta_reduction(lambda);
            }
            App(lhs, rhs) => {

                self.beta_reduction(lhs);
                self.beta_reduction(rhs);

                // if the left term is a constant, we may want to unwrap it
                if let Const(name) = self.lambda_storage[lhs].clone() {
                    let const_value = self.constants[&name];
                    if let Pi(..) = &self.lambda_storage[const_value.1] { // if it's a pi-type, defintly unwrap it!
                        self.deep_copy_at(self.constants[&name].0,lhs);
                    // But because a `(forall X. P)` is of type Type, we also need to check other case "more brute-like". not a perfect heristic
                    } else if let Lam(..) | Fix(..) | Pi(..) | Match(..) = &self.lambda_storage[const_value.0] {
                        self.deep_copy_at(self.constants[&name].0,lhs);
                    }
                }

                if self.reduce_fixpoint(lambda) { // Try to reduce a pottential fix point. If suceed, reduce again everything
                    return self.beta_reduction(lambda);
                }

                // Otherwise, check if it's a lambda abstraction
                match &self.lambda_storage[lhs] {
                    Lam(_, _, lhs) | Pi(_, _, lhs) => {
                        self.lambda_storage[lambda] = self.replace(*lhs, rhs);
                        self.beta_reduction(lambda); // reduce the new redexes that can appear
                    }
                    _ => self.beta_reduction(rhs), // can't reduce application of term that aren't abstractions
                }
            }
            Hole => (),
            Constr(_, _ , t) => {
                self.beta_reduction(t);
            }
            Match(t, _, _, _, v) => {
                self.beta_reduction(t);
                // Unfold a pottential constant
                if let Const(name) = self.lambda_storage[t].clone() {
                    self.deep_copy_at(self.constants[&name].0,t);
                }
                // we try to match some arm
                for (pi, ei) in v.iter() {
                    let t_node = self.shift_index(pi.bound_vars().len() as isize - 1, t);
                    let t = self.insert_node(t_node);
                    if let Some(mut bound_vars) = self.pattern_match(t, pi) {
                        self.lambda_storage[lambda] = self.lambda_storage[*ei].clone();
                        while let Some(v) = bound_vars.pop() {
                            self.lambda_storage[lambda] = self.replace(lambda, v);
                        }
                        return self.beta_reduction(lambda);
                    }
                }
                // if we get there, this means we were unable to match,
                // we must reduce all branches
                for (_, ei) in v.iter() {
                    self.beta_reduction(*ei);
                }
            }
            Fix(name, args,decreasing, t, body) => {
                for (_, i) in args{
                    self.beta_reduction(i);
                }
                self.beta_reduction(t);
                self.beta_reduction(body);
            }
        }
    }


}

#[cfg(test)]
mod tests {
    use super::{GlobalContext, LambdaTerm, Pattern};

    #[test]
    fn test_shift_zero() {
        let id = LambdaTerm::Abstraction(
            ("x".to_owned(), 0),
            Box::new(LambdaTerm::Type(0)),
            Box::new(LambdaTerm::Variable(("x".to_owned(), 0))),
        );
        let l0 = LambdaTerm::Application(Box::new(id.clone()), Box::new(id.clone()));
        let l1 = LambdaTerm::Application(Box::new(l0.clone()), Box::new(l0.clone()));
        let l2 = LambdaTerm::Application(Box::new(id.clone()), Box::new(l1.clone()));
        let fst = LambdaTerm::Abstraction(
            ("x".to_owned(), 0),
            Box::new(LambdaTerm::Type(0)),
            Box::new(LambdaTerm::Abstraction(
                ("y".to_owned(), 0),
                Box::new(LambdaTerm::Type(0)),
                Box::new(LambdaTerm::Variable(("x".to_owned(), 0))),
            )),
        );

        let snd = LambdaTerm::Abstraction(
            ("x".to_owned(), 0),
            Box::new(LambdaTerm::Type(0)),
            Box::new(LambdaTerm::Abstraction(
                ("y".to_owned(), 0),
                Box::new(LambdaTerm::Type(0)),
                Box::new(LambdaTerm::Variable(("y".to_owned(), 0))),
            )),
        );

        let lambdas = [id, l0, l1, l2, fst, snd];
        for lambda in lambdas {
            let mut context = GlobalContext::new();
            let Ok(original) = context.insert_term(lambda) else {panic!("Insert failed")};
            let node = context.shift_index(0, original);
            let shifted = context.insert_node(node);
            assert!(context.deep_equality(original, shifted))
        }
    }

    #[test]
    fn test_beta_reduction() {
        let id = LambdaTerm::Abstraction(
            ("x".to_owned(), 0),
            Box::new(LambdaTerm::Prop),
            Box::new(LambdaTerm::Variable(("x".to_owned(), 0))),
        );
        let l0 = LambdaTerm::Application(Box::new(id.clone()), Box::new(id.clone()));
        let l1 = LambdaTerm::Application(Box::new(l0.clone()), Box::new(l0.clone()));
        let l2 = LambdaTerm::Application(Box::new(id.clone()), Box::new(l1.clone()));
        let fst = LambdaTerm::Abstraction(
            ("x".to_owned(), 0),
            Box::new(LambdaTerm::Prop),
            Box::new(LambdaTerm::Abstraction(
                ("y".to_owned(), 0),
                Box::new(LambdaTerm::Prop),
                Box::new(LambdaTerm::Variable(("x".to_owned(), 0))),
            )),
        );

        let snd = LambdaTerm::Abstraction(
            ("x".to_owned(), 0),
            Box::new(LambdaTerm::Prop),
            Box::new(LambdaTerm::Abstraction(
                ("y".to_owned(), 0),
                Box::new(LambdaTerm::Prop),
                Box::new(LambdaTerm::Variable(("y".to_owned(), 0))),
            )),
        );

        let fst_app = LambdaTerm::Application(
            Box::new(LambdaTerm::Application(
                Box::new(fst.clone()),
                Box::new(fst.clone()),
            )),
            Box::new(snd.clone()),
        );
        let snd_app = LambdaTerm::Application(
            Box::new(LambdaTerm::Application(
                Box::new(snd.clone()),
                Box::new(fst.clone()),
            )),
            Box::new(snd.clone()),
        );

        let lambdas = [
            (id.clone(), id.clone()),
            (l0, id.clone()),
            (l1, id.clone()),
            (l2, id),
            (fst_app, fst),
            (snd_app, snd),
        ];
        for (lambda, expected) in lambdas {
            let mut context = GlobalContext::new();
            let Ok(l) = context.insert_term(lambda) else {panic!("Insert failed")};
            let Ok(e) = context.insert_term(expected) else {panic!("Insert failed")};
            context.beta_reduction(l);
            assert!(context.deep_equality(l, e));
        }
    }

    #[test]
    fn test_match(){
        //basic test
        
        /*test 1
            Inductive True: Type(0) := | Top: True.
            match Top as _ in True return True -> True with
            | Top => fun (x: True) => x
            end.

            the match block should reduce to
            fun (x: True) => x.
        */

        let mut context = GlobalContext::new();
        context.exec_command("Inductive True: Type(0) := |Top: True.").expect("Couldn't initialize inductive type");

        let v_true = LambdaTerm::Variable(("True".to_owned(), 0));
        let nx = ("x".to_owned(), 0);
        let vx = LambdaTerm::Variable(nx.clone());
        let n_top = ("Top".to_owned(), 0);
        let v_top = LambdaTerm::Variable(n_top.clone());
        let n_empty = ("".to_owned(), 0);
        let n_true = ("True".to_owned(), 0);
        let p_true = Pattern::Var(n_true); 
        let identity = LambdaTerm::Abstraction(nx, Box::new(v_true.clone()), Box::new(vx.clone()));
        let identity_type = LambdaTerm::Pi(n_empty.clone(), Box::new(v_true.clone()), Box::new(v_true.clone()));
        let p_top = Pattern::Var(n_top);
        let lambda_match = LambdaTerm::Match(Box::new(v_top.clone()), n_empty, p_true, Box::new(identity_type.clone()), vec![(p_top, identity.clone())]);

        let node_match = context.insert_term(lambda_match).expect("Insert failed");
        context.beta_reduction(node_match);
        let node_identity = context.insert_term(identity).expect("Insert failed");
        assert!(context.deep_equality(node_match, node_identity));
    }

    #[test]
    fn test_match2(){
        
        /*test 2
            Inductive Bool: Type(0) := | True: Bool | False: Bool.
            match True as _ in Bool return Bool with
            | True => True
            | False => False
            end.

            the match block should reduce to
            True.
        */

        let mut context = GlobalContext::new();
        context.exec_command("Inductive Bool: Type(0) := | True: Bool | False: Bool.").expect("Couldn't initialize inductive type");

        let n_true = ("True".to_owned(), 0);
        let v_true = LambdaTerm::Variable(n_true.clone());
        let p_true = Pattern::Var(n_true);
        let n_false = ("False".to_owned(), 0);
        let v_false = LambdaTerm::Variable(n_false.clone());
        let p_false = Pattern::Var(n_false);
        let n_empty = ("".to_owned(), 0);
        let n_bool = ("Bool".to_owned(), 0);
        let p_bool = Pattern::Var(n_bool.clone());
        let v_bool = LambdaTerm::Variable(n_bool.clone());
        let lambda_match = LambdaTerm::Match(Box::new(v_true.clone()), n_empty, p_bool, Box::new(v_bool), vec![
            (p_true, v_true.clone()),
            (p_false, v_false.clone()),
        ]);

        let node_match = context.insert_term(lambda_match).expect("Insert failed");
        context.beta_reduction(node_match);
        let expected = v_true.clone();
        let node_expected = context.insert_term(expected).expect("Insert failed");
        assert!(context.deep_equality(node_match, node_expected));
    }

    #[test]
    fn test_match3(){
        //basic test
        
        /*test 3
            Inductive Bool: Type(0) := | True: Bool | False: Bool.
            match False as _ in Bool return Bool with
            | True => True
            | False => False
            end.

            the match block should reduce to
            False.
        */

        let mut context = GlobalContext::new();
        context.exec_command("Inductive Bool: Type(0) := | True: Bool | False: Bool.").expect("Couldn't initialize inductive type");

        let n_true = ("True".to_owned(), 0);
        let v_true = LambdaTerm::Variable(n_true.clone());
        let p_true = Pattern::Var(n_true);
        let n_false = ("False".to_owned(), 0);
        let v_false = LambdaTerm::Variable(n_false.clone());
        let p_false = Pattern::Var(n_false);
        let n_empty = ("".to_owned(), 0);
        let n_bool = ("Bool".to_owned(), 0);
        let p_bool = Pattern::Var(n_bool.clone());
        let v_bool = LambdaTerm::Variable(n_bool.clone());
        let lambda_match = LambdaTerm::Match(Box::new(v_false.clone()), n_empty, p_bool, Box::new(v_bool), vec![
            (p_true, v_true.clone()),
            (p_false, v_false.clone()),
        ]);

        let node_match = context.insert_term(lambda_match).expect("Insert failed");
        context.beta_reduction(node_match);
        let expected = v_false.clone();
        let node_expected = context.insert_term(expected).expect("Insert failed");
        assert!(context.deep_equality(node_match, node_expected));
    }
}
