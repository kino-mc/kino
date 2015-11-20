// Copyright 2015 Adrien Champion. See the COPYRIGHT file at the top-level
// directory of this distribution.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

/*! Type checking. */

use std::collections::HashMap ;

use term::{
  BindMaker, AppMaker, OpMaker, Type, Sym, Term
} ;
use term::zip::* ;
use term::real_term::Var as RVar ;

use super::parse::Context ;

/** Function passed to `fold` over terms for type checking. */
fn checker(
  context: & Context,
  state: & Option<HashMap<Sym, Type>>,
  sig: & Option<HashMap<Sym, Type>>,
  step: Step<(Term, Type)>,
  bindings: & HashMap<Sym, (Term, Type)>,
  quantified: & HashMap<Sym, Type>,
) -> Result<(Term, Type), String> {
  use term::zip::Step::* ;
  match step {

    /* Application. */
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

    /* Operator. */
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

    /* Let binding. */
    Let(bindings, (kid, typ)) => {
      let mut nu_bindings = Vec::with_capacity(bindings.len()) ;
      for (sym, (term,_)) in bindings {
        nu_bindings.push( (sym, term) )
      } ;
      Ok( (
        context.factory().let_b(nu_bindings, kid), typ
      ) )
    },

    /* Universal quantifier. */
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

    /* Existential quantifier. */
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

    /* Constant. */
    C(cst) => {
      let typ = cst.typ().clone() ;
      Ok( (context.factory().mk_cst(cst), typ) )
    },

    /* Variable. */
    V(var) => {
      let typ = match * var.get() {
        RVar::SVar(ref sym, _) => {
          if let Some(ref state) = * state {
            if let Some(typ) = state.get(sym) {
              typ.clone()
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
            if let Some(typ) = sig.get(sym) {
              Some( typ.clone() )
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
                  if let Some( & (_, typ) ) = bindings.get(sym) {
                    typ.clone()
                  } else {
                  if let Some(typ) = quantified.get(sym) { typ.clone() } else {
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

/** Type checks a term. */
pub fn type_check(
  ctxt: & Context, term: & Term,
  state: Option<& [ (Sym, Type) ]>,
  sig: Option<& [ (Sym, Type) ]>,
) -> Result<Type, String> {
  let state = match state {
    None => None,
    Some(state) => {
      let mut map = HashMap::with_capacity(state.len()) ;
      for & (ref sym, ref typ) in state.iter() {
        map.insert(sym.clone(), typ.clone()) ; ()
      } ;
      Some(map)
    },
  } ;
  let sig = match sig {
    None => None,
    Some(sig) => {
      let mut map = HashMap::with_capacity(sig.len()) ;
      for & (ref sym, ref typ) in sig.iter() {
        map.insert(sym.clone(), typ.clone()) ; ()
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