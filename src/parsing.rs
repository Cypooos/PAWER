use pest::iterators::Pair;
use pest::{error::Error, iterators::Pairs};
use pest_derive::Parser;

use pest::Parser;

use crate::definitions::Pattern;
use crate::manager::Tactic;
use crate::{
    definitions::{LambdaTerm, VariableName},
    manager::Command,
};

// This file implement the parsing using the crate pest
// pest geenrate a series of `pair` or `pairs`. A pair is a grammar "rule"


// Generate the automaton
#[allow(dead_code)]
#[derive(Parser)]
#[grammar = "pest/grammar.pest"]
struct LambdaParser;

// transform a pair Rule::variable or Rule::name pair into a VariableName
// parse variables names like toto045 into (toto0,45)
pub fn pair_to_var(v: Pair<Rule>) -> VariableName {
    let stri = v.as_str();
    let chars = stri.chars().rev();
    let mut number_part = String::new();

    // Collect digits from the end until a non-digit is encountered
    for c in chars {
        if c.is_digit(10) {
            number_part.push(c);
        } else {
            break;
        }
    }

    // Reverse the number_part to get the correct order
    number_part = number_part.chars().rev().collect::<String>();
    let number_leading = number_part.chars().take_while(|&c| c == '0').count();
    
    // Case with no number
    if number_leading == number_part.len() {
        return (stri.to_string(),0)
    } else {
        let number = &stri[stri.len() - number_part.len()+number_leading..].parse::<usize>().unwrap();
        let text_part = &stri[..stri.len() - number_part.len()+number_leading];
        (text_part.to_string(), *number)
    }
    
}


pub fn pair_to_typed_vars(vs: Pair<Rule>) -> Vec<(VariableName, LambdaTerm)> {
    let mut inside = vs.into_inner().into_iter();
    let ty = pair_to_expr(inside.next_back().unwrap());
    inside.map(|name| {
        (pair_to_var(name), ty.clone())
    }).collect()
}

pub fn pair_to_typed_vars_list(vsl: Pair<Rule>) -> Vec<(VariableName, LambdaTerm)> {
    vsl.into_inner().map(pair_to_typed_vars).flatten().collect()
}


pub fn pair_to_pattern(v:Pairs<Rule>) -> Pattern {
    let mut cu = v.map(|x| {
        match x.as_rule() {
            Rule::p_wild => Pattern::Var(("".to_owned(),0)),
            Rule::pattern => pair_to_pattern(x.into_inner()),
            Rule::variable => Pattern::Var(pair_to_var(x.into_inner().next().unwrap())),
            _ => unreachable!("In pair_to_pattern, rule {:?}",x.as_rule())
        }
    });
    let fst = cu.next().unwrap();
    cu.fold(fst, |old, new| Pattern::App(Box::new(old), Box::new(new)))
}

pub fn pair_to_expr(v: Pair<Rule>) -> LambdaTerm {
    let r = v.as_rule();
    let mut inside = v.into_inner();
    match r {
        Rule::forall => {
            let args = inside.next().unwrap();
            let typed_vars_list = match args.as_rule() {
                Rule::typed_vars => pair_to_typed_vars(args),
                Rule::typed_vars_list => pair_to_typed_vars_list(args),
                _ => unreachable!(),
            };
            let mut otp = pair_to_expr(inside.next().unwrap());
            for (name, ty) in typed_vars_list.into_iter().rev() {
                otp = LambdaTerm::Pi(name, Box::new(ty), Box::new(otp))
            }
            otp
        },
        Rule::func => {
            let args = inside.next().unwrap();
            let typed_vars_list = match args.as_rule() {
                Rule::typed_vars => pair_to_typed_vars(args),
                Rule::typed_vars_list => pair_to_typed_vars_list(args),
                _ => unreachable!(),
            };
            let mut otp = pair_to_expr(inside.next().unwrap());
            for (name, ty) in typed_vars_list.into_iter().rev() {
                otp = LambdaTerm::Abstraction(name, Box::new(ty), Box::new(otp))
            }
            otp
        },
        Rule::match_ => {
            let to_match = Box::new(pair_to_expr(inside.next().unwrap()));
            let var = pair_to_var(inside.next().unwrap());
            let pat = pair_to_pattern(inside.next().unwrap().into_inner());
            let arity = Box::new(pair_to_expr(inside.next().unwrap()));

            let v = inside.next().unwrap().into_inner().map(|x| {
                    let mut inss = x.into_inner();
                    (pair_to_pattern(inss.next().unwrap().into_inner()),
                     pair_to_expr(inss.next().unwrap()))
                } ).collect();
            
            LambdaTerm::Match(
                to_match,
                var,
                pat,
                arity,
                v
            )
        }
        Rule::fix => {
            let name = pair_to_var(inside.next().unwrap());
            let args = pair_to_typed_vars_list(inside.next().unwrap());
            let stru = pair_to_var(inside.next().unwrap());
            let type_ = pair_to_expr(inside.next().unwrap());
            let lamb = pair_to_expr(inside.next().unwrap());
            LambdaTerm::Fix(name,args,stru,Box::new(type_),Box::new(lamb))
        }
        Rule::implies => {
            LambdaTerm::Pi(
                ("".to_owned(), 0),
                Box::new(pair_to_expr(inside.next().unwrap())),
                Box::new(pair_to_expr(inside.next().unwrap())),
            )
        },
        Rule::app => 
        {
            let root =pair_to_expr(inside.next().unwrap());
            inside.fold(root, |lambda, x| LambdaTerm::Application(
                Box::new(lambda),
                Box::new(pair_to_expr(x)),
            ))
        }
        Rule::lprop => LambdaTerm::Prop,
        Rule::lset => LambdaTerm::Set,
        Rule::variable => LambdaTerm::Variable(pair_to_var(inside.next().unwrap())),
        Rule::ltype => {
            let n = usize::from_str_radix(inside.next().unwrap().as_str(), 10).unwrap();
            LambdaTerm::Type(n)
        }
        _ => unreachable!("Parsing expression not implemeted"),
    }
}

fn pair_to_tactic(pair: Pair<Rule>) -> Tactic {
    let r = pair.as_rule();
    let mut inside = pair.into_inner();
    match r {
        Rule::exact => Tactic::Exact(pair_to_expr(inside.next().unwrap())),
        Rule::intro => Tactic::Intro(inside.next().map(pair_to_var)),
        Rule::intros => Tactic::Intros(inside.map(pair_to_var).collect()),
        Rule::apply => Tactic::Apply(pair_to_expr(inside.next().unwrap())),
        Rule::cut => Tactic::Cut(pair_to_expr(inside.next().unwrap())),
        Rule::unfold => Tactic::Unfold(pair_to_var(inside.next().unwrap())),
        Rule::simpl => Tactic::Simpl,
        Rule::induction => Tactic::Induction(pair_to_var(inside.next().unwrap())),
        _ => unreachable!("Unknown tactic {:?}", r),
    }
}

fn pair_to_command(comm_pair: Pair<Rule>) -> Command {
    let r = comm_pair.as_rule();
    let mut inside = comm_pair.into_inner();
    return match r {
        Rule::EOI => unreachable!("Empty Command {:?}", r),
        Rule::goal => Command::Goal(pair_to_expr(inside.next().unwrap())),
        Rule::theorem => {
            let name = pair_to_var(inside.next().unwrap());
            let lam = pair_to_expr(inside.next().unwrap());
            Command::Theorem(name, lam)
        },
        Rule::check => Command::Check(pair_to_expr(inside.next().unwrap())),
        Rule::reduce => Command::Reduce(pair_to_expr(inside.next().unwrap())),
        Rule::qed => Command::Qed,
        Rule::clean => Command::Clean,
        Rule::cancel => Command::Cancel,
        Rule::tactic => Command::Tactic(pair_to_tactic(inside.next().unwrap())),
        Rule::define => {
            let name = pair_to_var(inside.next().unwrap());
            let define_vars = inside.next().unwrap();
            let typed_vars_list = match define_vars.into_inner().next() {
                Some(typed_var_list) => pair_to_typed_vars_list(typed_var_list),
                None => Vec::new(),
            };
            let mut lam = pair_to_expr(inside.next().unwrap());
            for (name, ty) in typed_vars_list.into_iter().rev() {
                lam = LambdaTerm::Abstraction(name, Box::new(ty), Box::new(lam))
            }
            Command::Definition(name, lam)
        },
        Rule::inductive => {
            let name = pair_to_var(inside.next().unwrap());
            let param_vars = inside.next().unwrap();
            let params_list = match param_vars.into_inner().next() {
                Some(typed_var_list) => pair_to_typed_vars_list(typed_var_list),
                None => Vec::new(),
            };

            let lambda = pair_to_expr(inside.next().unwrap());

            let r = inside.map(|x|{
                let mut t = x.into_inner();
                (pair_to_var(t.next().unwrap()),pair_to_expr(t.next().unwrap()))
            }).collect();

            Command::Inductive(name, params_list, lambda, r)
        },
        Rule::fixpoint => {
            let name = pair_to_var(inside.next().unwrap());
            let args = pair_to_typed_vars_list(inside.next().unwrap());
            let stru = pair_to_var(inside.next().unwrap());
            let type_ = pair_to_expr(inside.next().unwrap());
            let lamb = pair_to_expr(inside.next().unwrap());
            let defined = LambdaTerm::Fix(name.clone(),args,stru,Box::new(type_),Box::new(lamb));

            Command::Definition(name, defined)
        }
        Rule::print => {
            let lamb = pair_to_expr(inside.next().unwrap());
            Command::Print(lamb)
        }
        Rule::print_proof => {
            Command::PrintProof
        }
        Rule::search => {
            let to_search = inside.next().unwrap().as_str().to_owned();
            Command::Search(to_search)
        }
        _ => unreachable!("Unknown command {:?}", r),
    };
}

fn pairs_to_commands(pairs: Pairs<Rule>) -> Vec<Command> {
    let mut t = Vec::new();
    for comm_pair in pairs {
        if comm_pair.as_rule() == Rule::EOI {break;}
        t.push(pair_to_command(comm_pair))
    }
    t
}

pub fn parse_lambda(text: &str) -> Result<LambdaTerm, Error<Rule>> {
    let pairs = LambdaParser::parse(Rule::lambda_top, text)?.next().unwrap();
    let t = pair_to_expr(pairs);
    Ok(t)
}

#[allow(unused)]
pub fn parse_commands(text: &str) -> Result<Vec<Command>, Error<Rule>> {
    let pairs = LambdaParser::parse(Rule::commands_top, text)?;
    let t = pairs_to_commands(pairs);
    Ok(t)
}

pub fn parse_command(text: &str) -> Result<Command, Error<Rule>> {
    let pair = LambdaParser::parse(Rule::command_top, text)?
        .next()
        .unwrap();
    let t = pair_to_command(pair);
    Ok(t)
}

#[test]
fn commands() {
    for s in vec![
        "Qed. Goal forall A:Prop, A. Qed.",
        "Goal forall A:Prop, A. exact fun (A:Prop) => A. Qed.",
        "Check fun (A:Prop) => A........",
        "..Reduce (fun (A:Prop) => A) (fun (B:Prop) B)........",
        "Cancel. Qed.. Qed. Cancel.",
        "intro blahaj.",
        "intro.",
        "apply (fun (x:A) => A) x.",
        "cut A -> A -> A.",
    ] {
        let u = parse_commands(s);
        println!("{}\t->\t{:?}", s, u)
    }
}


#[test]
fn names() {
    use LambdaTerm::*;
    for (s,sol) in vec![
        ("xoxo",("xoxo",0)),
        ("he54he45",("he54he",45)),
        ("h21",("h",21)),
        ("h",("h",0)),
        ("h1",("h",1)),
        ("h0",("h0",0)),
        ("h01",("h0",1)),
        ("001",("00",1)), // hum weird edge case
        ("45",("",45)), // hum weird edge case
        ("0",("0",0)), 
        ] {
        let v = parse_lambda(s);
        assert_eq!(
            v,
            Ok(Variable((sol.0.to_owned(), sol.1)))
        )
    }
}

#[test]
fn basic_parsing() {
    use LambdaTerm::*;
    let b = |x| Box::new(x);
    let v = parse_lambda("forall x:A -> A, x x");
    assert_eq!(
        v,
        Ok(Pi(
            ("x".to_owned(), 0),
            b(Pi(
                ("".to_owned(), 0),
                b(Variable(("A".to_owned(), 0))),
                b(Variable(("A".to_owned(), 0)))
            )),
            b(Application(
                b(Variable(("x".to_owned(), 0))),
                b(Variable(("x".to_owned(), 0)))
            ))
        ))
    )
}

#[test]
fn forall_inside() {
    use LambdaTerm::*;
    let b = |x| Box::new(x);
    let v = parse_lambda("forall x: forall y:A,A, forall x:A,A");
    assert_eq!(
        v,
        Ok(Pi(
            ("x".to_owned(), 0),
            b(Pi(
                ("y".to_owned(), 0),
                b(Variable(("A".to_owned(), 0))),
                b(Variable(("A".to_owned(), 0)))
            )),
            b(Pi(
                ("x".to_owned(), 0),
                b(Variable(("A".to_owned(), 0))),
                b(Variable(("A".to_owned(), 0)))
            ))
        ))
    )
}

#[test]
fn chained_implies() {
    use LambdaTerm::*;
    let b = |x| Box::new(x);
    let v = parse_lambda("A -> (B -> C) -> D");
    assert_eq!(
        v,
        Ok(Pi(
            ("".to_owned(), 0),
            b(Variable(("A".to_owned(), 0))),
            b(Pi(
                ("".to_owned(), 0),
                b(Pi(
                    ("".to_owned(), 0),
                    b(Variable(("B".to_owned(), 0))),
                    b(Variable(("C".to_owned(), 0)))
                )),
                b(Variable(("D".to_owned(), 0)))
            ))
        ))
    )
}

#[test]
fn apps() {
    use LambdaTerm::*;
    let b = |x| Box::new(x);
    let v = parse_lambda("a b c");
    assert_eq!(
        v,
        Ok(Application(
            b(Application(b(Variable(("a".to_owned(), 0))),b(Variable(("b".to_owned(), 0))))),
            b(Variable(("c".to_owned(), 0))),
        ))
    )
}

#[test]
fn definition() {
    use Command::Definition;
    use LambdaTerm::*;
    let v = parse_command("Definition f (x:Prop) := x.");
    assert_eq!(
        v,
        Ok(Definition(
            ("f".to_owned(), 0),
            Abstraction(
                ("x".to_owned(), 0),
                Box::new(Prop),
                Box::new(Variable(("x".to_owned(), 0)))
            )
        ))
    )
}

#[test]
fn inductive_false() {
    use Command::Inductive;
    use LambdaTerm::*;
    let v = parse_command("Inductive False : Prop :=.");
    assert_eq!(
        v,
        Ok(Inductive(
            ("False".to_owned(), 0),
            vec![],
            Prop,
            vec![]
        ))
    )
}

#[test]
fn inductive_n() {
    use Command::Inductive;
    use LambdaTerm::*;
    let v = parse_command("Inductive N : Set := Z : N | S : N -> N.");
    assert_eq!(
        v,
        Ok(Inductive(
            ("N".to_owned(), 0),
            vec![],
            Set,
            vec![
                (("Z".to_owned(), 0),Variable(("N".to_owned(), 0))),
                (("S".to_owned(), 0),
                    Pi(("".to_owned(), 0),
                        Box::new(Variable(("N".to_owned(), 0))),
                        Box::new(Variable(("N".to_owned(), 0))))
                ),
            ]
        ))
    )
}

#[test]
fn inductive_eq() {
    
    use Command::Inductive;
    use LambdaTerm::*;
    let v = parse_command("Inductive eq (A:Prop) (x:A) : A -> Prop := eq_refl : eq A x x.");
    assert_eq!(
        v,
        Ok(Inductive(
            ("eq".to_owned(), 0),
            vec![
                (("A".to_owned(), 0),Prop),
                (("x".to_owned(), 0),Variable(("A".to_owned(), 0)))
            ],
            Pi(("".to_owned(), 0),
                Box::new(Variable(("A".to_owned(), 0))),
                Box::new(Prop),
            ),
            vec![
                (("eq_refl".to_owned(), 0),
                    Application(Box::new(
                        Application(Box::new(
                            Application(Box::new(
                                Variable(("eq".to_owned(),0))
                            ),Box::new(Variable(("A".to_owned(),0))))
                        ),Box::new(Variable(("x".to_owned(),0))))
                    ),Box::new(Variable(("x".to_owned(),0)))
                    )
                ),
            ]
        ))
    )
}

// Reduce match f x as y in T _ t return t with | _ => Prop end .
#[test]
fn match_e() {
    use Command::Reduce;
    use LambdaTerm::*;
    let v = parse_command("Reduce match f x as y in T _ t return t with | G a b => a | _ => kappa end.");
    assert_eq!(
        v,
        Ok(Reduce(
            Match(
                Box::new(Application(
                    Box::new(Variable(("f".to_owned(),0))),
                    Box::new(Variable(("x".to_owned(),0))),
                )),
                ("y".to_owned(),0),
                Pattern::App(
                    Box::new(Pattern::App(
                        Box::new(Pattern::Var(("T".to_owned(),0))),
                        Box::new(Pattern::Var(("".to_owned(),0))),
                    )),
                    Box::new(Pattern::Var(("t".to_owned(),0)))
                ),
                Box::new(Variable(("t".to_owned(),0))),
                vec![
                    (
                        Pattern::App(
                            Box::new(Pattern::App(
                                Box::new(Pattern::Var(("G".to_owned(),0))),
                                Box::new(Pattern::Var(("a".to_owned(),0))),
                            )),
                            Box::new(Pattern::Var(("b".to_owned(),0)))
                        ),
                        Variable(("a".to_owned(),0))
                    ),
                    (
                        Pattern::Var(("".to_owned(),0)),
                        Variable(("kappa".to_owned(),0))
                    )
                ]
            )
        ))
    )
}

#[test]
fn fix_add() {
    use Command::Check;
    use LambdaTerm::*;
    let v = parse_command("Check fix add (n m : nat) {struct n} : nat := Prop.");
    assert_eq!(
        v,
        Ok(Check(
            Fix(
                ("add".to_owned(),0),
                vec![
                    (("n".to_owned(),0),Variable(("nat".to_owned(),0))),
                    (("m".to_owned(),0),Variable(("nat".to_owned(),0))),
                ],
                ("n".to_owned(),0),
                Box::new(Variable(("nat".to_owned(),0))),
                Box::new(Prop)
            )
        ))
    )
}

#[test]
fn fixpoint_add() {
    use Command::Definition;
    use LambdaTerm::*;
    let v = parse_command("Fixpoint add (m n : nat) {struct n} : nat := Prop.");
    assert_eq!(
        v,
        Ok(Definition(
            ("add".to_owned(),0),
            Fix(
                ("add".to_owned(),0),
                vec![
                    (("m".to_owned(),0),Variable(("nat".to_owned(),0))),
                    (("n".to_owned(),0),Variable(("nat".to_owned(),0))),
                ],
                ("n".to_owned(),0),
                Box::new(Variable(("nat".to_owned(),0))),
                Box::new(Prop)
            )
        ))
    )
}

#[test]
fn forall_multivar() {
    use LambdaTerm::*;
    let v = parse_lambda("forall x y z:Prop, Prop");
    assert_eq!(
        v,
        Ok(Pi(
            ("x".to_owned(), 0), 
            Box::new(Prop), 
            Box::new(Pi(
                ("y".to_owned(), 0),
                Box::new(Prop),
                Box::new(Pi(
                    ("z".to_owned(), 0),
                    Box::new(Prop),
                    Box::new(Prop)
                ))
            ))
        ))
    );
}

