// Copyright 2015 Adrien Champion. See the COPYRIGHT file at the top-level
// directory of this distribution.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

/*! Checks what has been parsed makes sense.

See `parse::Context` for the description of the checks. */

use std::fmt ;

use term ;
use term::{ Sym, Var } ;
use term::real ;

use base::* ;
use parse::Context ;

use self::Error::* ;

/** Parse error. */
pub enum Error {
  /** Redefinition of identifier. */
  Redef(Item, Item),
  /** State var in define-fun. */
  SVarInDef(Var, FunDef),
  /** Use of unknown symbol in application. */
  UkCall(Item, Sym),
  /** Use of unknown state symbol. */
  UkState(Item),
  /** Use of unknown (state) variable. */
  UkVar(Var, Item),
  /** Use of unknown init identifier. */
  UkInit(Sys),
  /** Use of unknown trans identifier. */
  UkTrans(Sys),
  /** Inconsistent state between items. */
  IncState(Sys, Item),
  /** Use of unknown system identifier in check. */
  UkSys(Sym),
  /** Use of unknown pred identifier. */
  UkPred(Sym),
  /** Inconsistent predicate state in check. */
  IncPredState(Sys, Pred),
  /** Illegal next state variable in init. */
  NxtInit(Sym, Init),
  /** I/O error. */
  Io(::std::io::Error),
}
impl fmt::Display for Error {
  fn fmt(& self, fmt: & mut fmt::Formatter) -> fmt::Result {
    use base::Item::* ;
    use term::real::Var::* ;
    match * self {
      Redef(ref i1, ref i2) => {
        assert_eq!(i1.sym(), i2.sym()) ;
        let (sym, d1, d2) = (i1.sym(), i1.desc(), i2.desc()) ;
        if d1 == d2 {
          write!(fmt, "duplicate {} for {}", d1, sym)
        } else {
          write!(fmt, "{} for {} conflicts with previous {}", d2, sym, d1)
        }
      },
      SVarInDef(ref var, ref f) => write!(
        fmt, "use of state variable {} in define-fun {}", var, f.sym()
      ),
      UkCall(ref i, ref sym) => write!(
        fmt,
        "application of unknown function symbol {} in {} {}",
        sym, i.desc(), i.sym()
      ),
      UkState(ref i) => match i.state() {
        None => panic!(
          "unknown state stateless item {} {}", i.desc(), i.sym()
        ),
        Some(state) => write!(
          fmt, "unknown state {} in {} {}", state, i.desc(), i.sym()
        ),
      },
      UkVar(ref var, ref i) => match * var.get() {
        Var(_) => write!(
          fmt, "unknown nullary function symbol {} in {} {}",
          var, i.desc(), i.sym()
        ),
        SVar(_,_) => match i.state() {
          None => panic!(
            "unknown state variable {} in stateless item {} {}",
            var, i.desc(), i.sym()
          ),
          Some(state) => write!(
            fmt, "unknown state variable {} in {} {} over {}",
            var, i.desc(), i.sym(), state
          ),
        },
      },
      UkInit(ref sys) => write!(
        fmt, "unknown init predicate {} in system definition {}",
        sys.init(), sys.sym()
      ),
      UkTrans(ref sys) => write!(
        fmt, "unknown trans predicate {} in system definition {}",
        sys.trans(), sys.sym()
      ),
      IncState(ref sys, I(ref init)) => write!(
        fmt,
        "system definition {} has state {} but init predicate {} has state {}",
        sys.sym(), sys.state(), init.sym(), init.state()
      ),
      IncState(ref sys, T(ref trans)) => write!(
        fmt, "\
          system definition {} has state {} \
          but trans predicate {} has state {}\
        ",
        sys.sym(), sys.state(), trans.sym(), trans.state()
      ),
      IncState(ref sys, ref i) => panic!(
        "inconsistent state error between system {} and {} {}",
        sys.sym(), i.desc(), i.sym()
      ),
      UkSys(ref sym) => write!(fmt, "unknown system {} in check", sym),
      UkPred(ref sym) => write!(fmt, "unknown pred {} in check", sym),
      IncPredState(ref sys, ref pred) => write!(
        fmt, "\
          predicate {} over state {} \
          cannot be checked for system {} with state {}\
        ",
        pred.sym(), pred.state(), sys.sym(), sys.state()
      ),
      NxtInit(ref sym, ref init) => write!(
        fmt, "init definition {} uses state variable {} in next state",
        init.sym(), sym
      ),
      Io(ref e) => write!(fmt, "i/o error \"{}\"", e),
    }
  }
}

/** Checks that an identifier is unused. */
fn sym_unused(
  ctxt: & Context, i: & Item
) -> Result<(), Error> {
  match ctxt.item_of_sym(i.sym()) {
    None => Ok(()),
    Some(original) => Err( Redef(original, i.clone()) ),
  }
}

/** Checks that a variable is defined. That is, looks for a function symbol
declaration/definition for the variable's symbol with arity zero. */
fn var_defined(
  ctxt: & Context, sym: & Sym
) -> bool {
  use base::Callable::* ;
  match ctxt.get_callable(sym) {
    None => false,
    Some(& Dec(ref f)) => f.sig().len() == 0,
    Some(& Def(ref f)) => f.args().len() == 0,
  }
}

/** Checks that an application is defined. That is, looks for a function symbol
declaration/definition for a symbol with arity greater than zero. */
fn app_defined(
  ctxt: & Context, sym: & Sym
) -> bool {
  use base::Callable::* ;
  match ctxt.get_callable(sym) {
    None => false,
    Some(& Dec(ref f)) => f.sig().len() > 0,
    Some(& Def(ref f)) => f.args().len() > 0,
  }
}

/** Checks that a symbol is defined as an init or trans predicate. Used to
check the function symbol applications of init and trans predicates. */
fn sys_app_defined(
  ctxt: & Context, sym: & Sym
) -> bool {
  ctxt.get_init(sym).is_some() ||
  ctxt.get_trans(sym).is_some()
}

/** Checks that a state variables belongs to a state. */
fn svar_in_state(
  svar: & Sym, state: & State
) -> bool {
  for & (ref s, _) in state.args().iter() {
    if s == svar { return true }
  } ;
  false
}

/** Checks that a state is legal. */
fn check_state(
  ctxt: & Context, _: & State, i: & Item
) -> Result<(), Error> {
  sym_unused(ctxt,i)
}

/** Checks that a function declaration is legal. */
fn check_fun_dec(
  ctxt: & Context, _: & FunDec, i: & Item
) -> Result<(), Error> {
  sym_unused(ctxt,i)
}

/** Checks that a function definition is legal. */
fn check_fun_def(
  ctxt: & Context, fd: & FunDef, i: & Item
) -> Result<(), Error> {
  try!(sym_unused(ctxt,i)) ;
  let body = fd.body().body() ;
  // All symbols used in applications actually exist.
  for sym in body.apps.iter() {
    if ! app_defined(ctxt, sym) {
      return Err( UkCall(i.clone(), sym.clone()) )
    }
  } ;
  // No stateful var, all non-stateful vars exist.
  for var in body.vars.iter() {
    match * var.get() {
      real::Var::Var(ref sym) => {
        let mut exists = false ;
        if ! var_defined(ctxt, sym) {
          for & (ref dsym, _) in fd.args() {
            if dsym == sym { exists = true }
          }
        } else { exists = true } ;
        if ! exists {
          return Err( UkVar(var.clone(), i.clone()) )
        }
      },
      _ => return Err( SVarInDef(var.clone(), fd.clone()) ),
    }
  } ;
  Ok(())
}

/** Checks that a predicate definition is legal. */
fn check_pred(
  ctxt: & Context, pred: & Pred, i: & Item
) -> Result<(), Error> {
  try!(sym_unused(ctxt,i)) ;
  let state = match ctxt.get_state(pred.state()) {
    Some(s) => s,
    None => return Err( UkState(i.clone()) ),
  } ;
  let body = pred.body().body() ;
  // All symbols used in applications actually exist.
  for sym in body.apps.iter() {
    if ! app_defined(ctxt, sym) {
      return Err( UkCall(i.clone(), sym.clone()) )
    }
  } ;
  // Stateful var belong to state, non-stateful var exist.
  for var in body.vars.iter() {
    match * var.get() {
      // Non-stateful var exist.
      real::Var::Var(ref sym) => if ! var_defined(ctxt, sym) {
        return Err( UkVar(var.clone(), i.clone()) )
      },
      // Stateful var belong to state.
      // Next and current allowed.
      real::Var::SVar(ref sym, _) => if ! svar_in_state(sym, state) {
        return Err( UkVar(var.clone(), i.clone()) )
      },
    }
  } ;
  Ok(())
}

/** Checks that an init predicate definition is legal. */
fn check_init(
  ctxt: & Context, init: & Init, i: & Item
) -> Result<(), Error> {
  try!(sym_unused(ctxt,i)) ;
  let state = match ctxt.get_state(init.state()) {
    Some(s) => s,
    None => return Err( UkState(i.clone()) ),
  } ;
  let body = init.body().body() ;
  // All symbols used in applications actually exist.
  for sym in body.apps.iter() {
    if ( ! app_defined(ctxt, sym) ) && ( ! sys_app_defined(ctxt, sym) ) {
      return Err( UkCall(i.clone(), sym.clone()) )
    }
  } ;
  // Current stateful var belong to state, non-stateful var exist.
  for var in body.vars.iter() {
    match * var.get() {
      // Non-stateful var exist.
      real::Var::Var(ref sym) => if ! var_defined(ctxt, sym) {
        return Err( UkVar(var.clone(), i.clone()) )
      },
      // Next state variables are illegal.
      real::Var::SVar(ref sym, term::State::Next) => return Err(
        NxtInit(sym.clone(), init.clone())
      ),
      // Current stateful var belong to state.
      real::Var::SVar(ref sym, _) => if ! svar_in_state(sym, state) {
        return Err( UkVar(var.clone(), i.clone()) )
      },
    }
  } ;
  Ok(())
}

/** Checks that a trans predicate definition is legal. */
fn check_trans(
  ctxt: & Context, trans: & Trans, i: & Item
) -> Result<(), Error> {
  try!(sym_unused(ctxt,i)) ;
  let state = match ctxt.get_state(trans.state()) {
    Some(s) => s,
    None => return Err( UkState(i.clone()) ),
  } ;
  let body = trans.body().body() ;
  // All symbols used in applications actually exist.
  for sym in body.apps.iter() {
    if ( ! app_defined(ctxt, sym) ) && ( ! sys_app_defined(ctxt, sym) ) {
      return Err( UkCall(i.clone(), sym.clone()) )
    }
  } ;
  // Stateful var belong to state, non-stateful var exist.
  for var in body.vars.iter() {
    match * var.get() {
      // Non-stateful var exist.
      real::Var::Var(ref sym) => if ! var_defined(ctxt, sym) {
        return Err( UkVar(var.clone(), i.clone()) )
      },
      // Stateful var belong to state.
      // Next and current allowed.
      real::Var::SVar(ref sym, _) => if ! svar_in_state(sym, state) {
        return Err( UkVar(var.clone(), i.clone()) )
      },
    }
  } ;
  Ok(())
}

/** Checks that a system definition is legal. */
fn check_sys(
  ctxt: & Context, sys: & Sys, i: & Item
) -> Result<(), Error> {
  try!(sym_unused(ctxt,i)) ;
  let state = match ctxt.get_state(sys.state()) {
    Some(s) => s,
    None => return Err( UkState(i.clone()) ),
  } ;
  let init = sys.init() ;
  let trans = sys.trans() ;
  match ctxt.get_init(init) {
    None => return Err( UkInit(sys.clone()) ),
    Some(init) => if init.state() != state.sym() {
      return Err( IncState(sys.clone(), Item::I(init.clone())) )
    },
  } ;
  match ctxt.get_trans(trans) {
    None => return Err( UkInit(sys.clone()) ),
    Some(trans) => if trans.state() != state.sym() {
      return Err( IncState(sys.clone(), Item::T(trans.clone())) )
    },
  } ;
  Ok(())
}

/** Checks that an item is legal. */
pub fn check_item(
  ctxt: & Context, i: & Item
) -> Result<(), Error> {
  use base::Item::* ;
  match * i {
    St(ref state) => check_state(ctxt, state, i),
    FDc(ref f) => check_fun_dec(ctxt, f, i),
    FDf(ref f) => check_fun_def(ctxt, f, i),
    P(ref pred) => check_pred(ctxt, pred, i),
    I(ref init) => check_init(ctxt, init, i),
    T(ref trans) => check_trans(ctxt, trans, i),
    S(ref sys) => check_sys(ctxt, sys, i),
  }
}

/** Checks that a check is legal. */
pub fn check_check(
  ctxt: & Context, & (ref sys, ref preds): & (Sym, Vec<Sym>)
) -> Result<(), Error> {
  let sys = match ctxt.get_sys(sys) {
    None => return Err( UkSys(sys.clone()) ),
    Some(sys) => sys,
  } ;
  for pred in preds.iter() {
    let pred = match ctxt.get_pred(pred) {
      None => return Err( UkPred(pred.clone()) ),
      Some(pred) => pred,
    } ;
    if sys.state() != pred.state() {
      return Err( IncPredState(sys.clone(), pred.clone()) )
    }
  } ;
  Ok(())
}