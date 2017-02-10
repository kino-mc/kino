// Copyright 2015 Adrien Champion. See the COPYRIGHT file at the top-level
// directory of this distribution.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! Type checking.

use std::collections::HashMap ;

use term::{
  BindMaker, AppMaker, OpMaker, Type, Sym, Term
} ;
use term::zip::* ;
use term::real_term::Var as RVar ;
use term::parsing::{ Spn, Spnd } ;

use super::parse::Context ;

/// Function passed to `fold` over terms for type checking.
fn checker(
  context: & Context,
  state: & Option<
    HashMap< Sym, (Spn, Spnd<Type>) >
  >,
  sig: & Option<
    HashMap< Sym, (Spn, Spnd<Type>) >
  >,
  step: Step<(Term, Type)>,
  bindings: & [
    HashMap< Sym, (Term, Type) >
  ],
  quantified: & [ HashMap<Sym, Type> ],
) -> Result<(Term, Type), String> {
  use term::zip::Step::* ;
  match step {

    // Application.
    App(sym, kids) => {
      let (mut nu_kids, mut types) = (
        Vec::with_capacity(kids.len()),
        Vec::with_capacity(kids.len())
      ) ;
      for (term, typ) in kids {
        nu_kids.push(term) ;
        types.push(typ)
      } ;
      match context.get_callable(& sym) {
        Some(fun) => match fun.type_check(& types) {
          Ok(typ) => Ok( (
            context.factory().app(sym, nu_kids), typ
          ) ),
          Err( (arg, bla) ) => return Err(
            format!("{}\nparameter {}:\n  {}", bla, arg, nu_kids[arg])
          ),
        },
        None => return Err(
          format!("application of unknown function symbol {}", sym)
        ),
      }
    },

    // Operator.
    Op(op, kids) => {
      let (mut nu_kids, mut types) = (
        Vec::with_capacity(kids.len()),
        Vec::with_capacity(kids.len())
      ) ;
      for (term, typ) in kids {
        nu_kids.push(term) ;
        types.push(typ)
      } ;
      match op.type_check(& types) {
        Ok(typ) => Ok( (
          context.factory().op(op, nu_kids), typ
        ) ),
        Err( (args, mut bla) ) => {
          if let Some(args) = args {
            for arg in args {
              bla = format!("{}\nargument {}:\n  {}", bla, arg, nu_kids[arg])
            } ;
          } ;
          return Err(bla)
        },
      }
    },

    // Let binding.
    Let(bindings, (kid, typ)) => {
      let mut nu_bindings = Vec::with_capacity(bindings.len()) ;
      for (sym, (term,_)) in bindings {
        nu_bindings.push( (sym, term) )
      } ;
      nu_bindings.reverse() ;
      Ok( (
        context.factory().let_b(nu_bindings, kid), typ
      ) )
    },

    // Universal quantifier.
    Forall(qf, (kid, typ)) => {
      if typ != Type::Bool {
        return Err(
          format!(
            "forall quantifier expects Bool but got {}\n\
              argument:\n  {}",
            typ, kid
          )
        )
      } ;
      Ok( (
        context.factory().forall(qf, kid), typ
      ) )
    },

    // Existential quantifier.
    Exists(qf, (kid, typ)) => {
      if typ != Type::Bool {
        return Err(
          format!(
            "exists quantifier expects Bool but got {}\n\
              argument:\n  {}",
            typ, kid
          )
        )
      } ;
      Ok( (
        context.factory().exists(qf, kid), typ
      ) )
    },

    // Constant.
    C(cst) => {
      let typ = cst.typ().clone() ;
      Ok( (context.factory().mk_cst(cst), typ) )
    },

    // Variable.
    V(var) => {
      let typ = match * var.get() {
        RVar::SVar(ref sym, _) => {
          if let Some(ref state) = * state {
            if let Some( & (_, ref typ) ) = state.get(sym) {
              typ.get().clone()
            } else {
              return Err(
                format!("unknown state variable {}", sym)
              )
            }
          } else {
            return Err(
              format!("unexpected state variable ({})", sym)
            )
          }
        },
        RVar::Var(ref sym) => {
          match if let Some(ref sig) = * sig {
            if let Some( & (_, ref typ) ) = sig.get(sym) {
              Some( typ.get().clone() )
            } else {
              None
            }
          } else { None } {
            Some(typ) => typ,
            None => {
              match context.get_callable(& sym) {
                Some(fun) => match fun.type_check(& []) {
                  Ok(typ) => typ,
                  Err( (_, bla) ) => return Err( format!("{}", bla) ),
                },
                None => {
                  if let Some( & (_, typ) ) = extract(sym, bindings) {
                    typ.clone()
                  } else {
                    if let Some(typ) = extract(sym, quantified) {
                      typ.clone()
                    } else {
                        return Err(format!("unknown symbol {}", sym))
                    }
                  }
                }
              }
            }
          }
        },
      } ;
      Ok( ( context.factory().mk_var(var), typ ) )
    },
  }
}

/// Type checks a term.
pub fn type_check(
  ctxt: & Context, term: & Term,
  state: Option<& [ ( Spnd<Sym>, Spnd<Type> ) ]>,
  sig: Option<& [ ( Spnd<Sym>, Spnd<Type> ) ]>,
) -> Result<Type, String> {
  let state = match state {
    None => None,
    Some(state) => {
      let mut map = HashMap::with_capacity(state.len()) ;
      for & (ref sym, ref typ) in state.iter() {
        let (sym, spn) = sym.extract() ;
        map.insert( sym, (spn, typ.clone()) ) ; ()
      } ;
      Some(map)
    },
  } ;
  let sig = match sig {
    None => None,
    Some(sig) => {
      let mut map = HashMap::with_capacity(sig.len()) ;
      for & (ref sym, ref typ) in sig.iter() {
        let (sym, spn) = sym.extract() ;
        map.insert( sym, (spn, typ.clone()) ) ; ()
      } ;
      Some(map)
    },
  } ;
  match ::term::zip::fold_info(
    move |step, binding, quantified| checker(
      ctxt, & state, & sig, step, binding, quantified
    ),
    term
  ) {
    Ok( (_, typ) ) => Ok(typ),
    Err(e) => Err(e),
  }
}



/// Tests the evaluator.
#[cfg(test)]
pub mod test {
  use term::gen::* ;
  use term::* ;
  use base::Callable ;
  use parse::{ Context, Res } ;

  /// Generates random terms to check the evaluator.
  // #[test]
  pub fn _rand_terms_fault_conf() {
    use std::fs::File ;
    use std::collections::HashMap ;

    let file = "rsc/simple/fault_conf.vmt" ;
    let factory = Factory::mk() ;
    let mut context = Context::mk(factory.clone(), 1000) ;

    println!("| opening file {}", file) ;
    match File::open(file) {
      Ok(mut f) => {
        println!("| parsing") ;
        match context.read(& mut f) {
          Ok(res) => {
            println!("| > done") ;
            match res {

              Res::Check(sys, _) => {

                // Throw in some constants.
                let (
                  zero, one, two, three, four, five, six, seven, eight, ftwo
                ) = (
                  Int::parse_bytes(b"0",  10).unwrap(),
                  Int::parse_bytes(b"1",  10).unwrap(),
                  Int::parse_bytes(b"2",  10).unwrap(),
                  Int::parse_bytes(b"3",  10).unwrap(),
                  Int::parse_bytes(b"4", 10).unwrap(),
                  Int::parse_bytes(b"5",  10).unwrap(),
                  Int::parse_bytes(b"6",  10).unwrap(),
                  Int::parse_bytes(b"7",  10).unwrap(),
                  Int::parse_bytes(b"8",  10).unwrap(),
                  Int::parse_bytes(b"42", 10).unwrap()
                ) ;
                let mut bool_terms = TermSet::new() ;
                bool_terms.extend(
                  vec![ factory.cst(true ), factory.cst(false) ]
                ) ;
                let mut int_terms = TermSet::new() ;
                int_terms.extend(
                  vec![
                    factory.cst(zero.clone()),
                    factory.cst(one.clone()),
                    factory.cst(two.clone()),
                    factory.cst(three.clone()),
                    factory.cst(four.clone()),
                    factory.cst(five.clone()),
                    factory.cst(six.clone()),
                    factory.cst(seven.clone()),
                    factory.cst(eight.clone()),
                    factory.cst(ftwo.clone())
                  ]
                ) ;
                let mut rat_terms = TermSet::new() ;
                rat_terms.extend(
                  vec![
                    factory.cst( Rat::new(zero.clone(), one.clone()) ),
                    factory.cst( Rat::new(ftwo.clone(), one.clone()) ),
                    factory.cst( Rat::new(ftwo.clone(), two.clone()) ),
                    factory.cst( Rat::new(three.clone(), ftwo.clone()) ),
                    factory.cst( Rat::new(two.clone(), three.clone()) ),
                    factory.cst( Rat::new(seven.clone(), one.clone()) ),
                    factory.cst( Rat::new(eight.clone(), ftwo.clone()) ),
                    factory.cst( Rat::new(five.clone(), three.clone()) ),
                    factory.cst( Rat::new(six.clone(), one.clone()) ),
                    factory.cst( Rat::new(one.clone(), seven.clone()) ),
                    factory.cst( Rat::new(ftwo.clone(), six.clone()) ),
                    factory.cst( Rat::new(ftwo.clone(), eight.clone()) ),
                    factory.cst( Rat::new(one.clone(), one.clone()) ),
                    factory.cst( Rat::new(one.clone(), eight.clone()) ),
                    factory.cst( Rat::new(seven.clone(), two.clone()) )
                  ]
                ) ;


                let mut term_map = HashMap::new() ;
                term_map.insert(Type::Bool, bool_terms) ;
                term_map.insert(Type::Int, int_terms) ;
                term_map.insert(Type::Rat, rat_terms) ;

                // Add variable definitions to map.
                for call in sys.calls().get().iter() {
                  match * * call {
                    Callable::Dec(_) => (),
                    Callable::Def(ref def) => {
                      // Only want variables.
                      if def.args().is_empty() {
                        match term_map.get_mut(def.typ()) {
                          Some(set) => {
                            set.insert(
                              factory.var(def.sym().get().clone())
                            ) ;
                            ()
                          },
                          None => panic!(
                            "unexpected type {} (in define-fun {})",
                            def.typ(), def.sym()
                          ),
                        }
                      }
                    },
                  }
                } ;

                // Add svars to map.
                for & (ref sym, ref typ) in sys.state().args() {
                  match term_map.get_mut(typ) {
                    Some(set) => {
                      set.insert(
                        factory.svar(sym.get().clone(), State::Curr)
                      ) ;
                      set.insert(
                        factory.svar(sym.get().clone(), State::Next)
                      ) ;
                      ()
                    },
                    None => panic!(
                      "unexpected type {} (state variable {})",
                      typ, sym
                    ),
                  }
                } ;

                // Create generator.
                let mut gen = TermGen::random(factory, term_map) ;

                let (term_cnt, depth) = (30, 20) ;

                // Generating terms, type checking them.
                for t in vec![ Type::Bool, Type::Int, Type::Rat ] {
                  println!("| generating {} terms of type {}", term_cnt, t) ;
                  println!("| max depth is {}", depth) ;
                  let terms = gen.generate(t, term_cnt, Some(depth)) ;
                  println!("| > done ({})", terms.len()) ;
                  for term in terms {
                    println!("") ;
                    println!("| > term: {}", term) ;
                    println!("|   type checking") ;
                    match super::type_check(
                      & context, & term, Some(sys.state().args()), None
                    ) {
                      Ok(typ) => if typ != t {
                        panic!("| > expected {}, got {}", t, typ)
                      } else {
                        println!("| > ok")
                      },
                      Err(e) => {
                        panic!("| > expected {}, got error {}", t, e)
                      },
                    }
                  } ;
                }

              },

              _ => panic!(
                "expected a check, got {:?}", res
              ),
            }
          },
          Err(e) => {
            println!("could not parse input file:") ;
            for line in format!("{}", e).lines() {
              println!("| {}", line)
            } ;
            panic!("could not parse test file")
          },
        }
      },

      Err(e) => panic!("could not open test file: {}", e),
    }
  }
}