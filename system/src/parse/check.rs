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
use std::rc::Rc ;
use std::collections::HashSet ;

use term::{ TermAndDep, Type, Sym, Var, Term } ;
use term::real ;

use base::* ;
use super::{ Context, CanAdd } ;

use self::Error::* ;

/** Parse error. */
pub enum Error {
  /** Redefinition of identifier. */
  Redef(Sym, & 'static str, & 'static str),
  /** State var in define-fun. */
  SVarInDef(Var, Sym),
  /** Use of unknown symbol in application. */
  UkCall(Sym, Sym, & 'static str),
  /** Use of unknown (state) variable. */
  UkVar(Var, Sym, & 'static str),
  /** Use of unknown system identifier in check. */
  UkSys(Sym),
  /** Use of unknown prop identifier. */
  UkProp(Sym),
  /** Inconsistent property state in check. */
  IncPropState(Rc<Sys>, Rc<Prop>),
  /** Illegal next state variable in init. */
  NxtInit(Sym, Sym),
  /** Uknown system call in system definition. */
  UkSysCall(Sym, Sym),
  /** Inconsistent arity of system call in system definition. */
  IncSysCall(Sym, usize, Sym, usize),
  /** I/O error. */
  Io(::std::io::Error),
}
impl fmt::Display for Error {
  fn fmt(& self, fmt: & mut fmt::Formatter) -> fmt::Result {
    use term::real::Var::* ;
    match * self {
      Redef(ref sym, ref original, ref redef) => write!(
        fmt, "{} for {} conflicts with previous {}", sym, original, redef
      ),
      SVarInDef(ref var, ref sym) => write!(
        fmt, "use of state variable {} in define-fun {}", var, sym
      ),
      UkCall(ref call_sym, ref sym, ref desc) => write!(
        fmt, "application of unknown function symbol {} in {} {}",
        call_sym, desc, sym
      ),
      UkVar(ref var, ref sym, ref desc) => match * var.get() {
        Var(_) => write!(
          fmt, "unknown nullary function symbol {} in {} {}",
          var, desc, sym
        ),
        SVar(_,_) => write!(
          fmt, "unknown state variable {} in {} {}", var, desc, sym
        ),
      },
      UkSys(ref sym) => write!(fmt, "unknown system {} in check", sym),
      UkProp(ref sym) => write!(fmt, "unknown prop {} in check", sym),
      IncPropState(ref sys, ref prop) => write!(
        fmt, "\
          property {} over system {} \
          cannot be checked for system {} with state {}\
        ",
        prop.sym(), prop.sys().sym(), sys.sym(), sys.state()
      ),
      NxtInit(ref var_sym, ref sym) => write!(
        fmt, "init definition {} uses state variable {} in next state",
        sym, var_sym
      ),
      /** Uknown system call in system definition. */
      UkSysCall(ref sub_sym, ref sym) => write!(
        fmt, "unknown system call to {} in {} {}",
        sub_sym, sym, super::sys_desc
      ),
      /** Inconsistent arity of system call in system definition. */
      IncSysCall(ref sub_sym, ref arity, ref sym, ref arg_count) => write!(
        fmt, "\
          illegal system call to {} in {} {}: \
          {} parameters given but {} has arity {}\
        ", sub_sym, super::sys_desc, sym, arg_count, sub_sym, arity
      ),
      Io(ref e) => write!(fmt, "i/o error \"{}\"", e),
    }
  }
}

/** Checks that an identifier is unused. */
macro_rules! check_sym {
  ($ctxt:expr, $sym:expr, $desc:expr) => (
    match $ctxt.sym_unused(& $sym) {
      None => (),
      Some(original) => return Err(
        Redef($sym, original, $desc)
      ),
    }
  )
}

/** Checks that a variable is defined. That is, looks for a function symbol
declaration/definition for the variable's symbol with arity zero. */
fn var_defined(
  ctxt: & Context, sym: & Sym
) -> bool {
  use base::Callable::* ;
  match ctxt.get_callable(sym) {
    None => false,
    Some(f) => match * * f {
      Dec(ref f) => f.sig().len() == 0,
      Def(ref f) => f.args().len() == 0,
    },
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
    Some(f) => match * * f {
      Dec(ref f) => f.sig().len() > 0,
      Def(ref f) => f.args().len() > 0,
    },
  }
}

/** Checks that a state variables belongs to a state. */
fn new_svar_in_state(
  svar: & Sym, state: & Args
) -> bool {
  for & (ref s, _) in state.args().iter() {
    if s == svar { return true }
  } ;
  false
}

/** Checks that a function declaration is legal. */
pub fn check_fun_dec(
  ctxt: & mut Context, sym: Sym, sig: Sig, typ: Type
) -> Result<(), Error> {
  let desc = super::uf_desc ;
  check_sym!(ctxt, sym, desc) ;
  ctxt.add_callable(
    Callable::Dec( Uf::mk(sym, sig, typ) )
  ) ;
  Ok(())
}

/** Checks that a function definition is legal. */
pub fn check_fun_def(
  ctxt: & mut Context, sym: Sym, args: Args, typ: Type, body: TermAndDep
) -> Result<(), Error> {
  let desc = super::fun_desc ;
  check_sym!(ctxt, sym, desc) ;
  let desc = super::fun_desc ;
  let mut funs = HashSet::new() ;
  // All symbols used in applications actually exist.
  for call_sym in body.apps.iter() {
    if ! app_defined(ctxt, call_sym) {
      return Err( UkCall(call_sym.clone(), sym, desc) )
    } else {
      // Don't care if it was already there.
      funs.insert(call_sym.clone()) ;
    }
  } ;
  // No stateful var, all non-stateful vars exist.
  for var in body.vars.iter() {
    match * var.get() {
      real::Var::Var(ref var_sym) => {
        let mut exists = false ;
        if ! var_defined(ctxt, var_sym) {
          for & (ref dsym, _) in args.args() {
            if dsym == var_sym { exists = true }
          }
        } else { exists = true } ;
        if ! exists {
          return Err( UkVar(var.clone(), sym, desc) )
        }
      },
      _ => return Err( SVarInDef(var.clone(), sym) ),
    }
  } ;
  ctxt.add_callable(
    Callable::Def( Fun::mk(sym, args, typ, body.term) )
  ) ;
  Ok(())
}

/** Checks that a proposition definition is legal. */
pub fn check_prop(
  ctxt: & mut Context, sym: Sym, sys: Sym, body: TermAndDep
) -> Result<(), Error> {
  let desc = super::prop_desc ;
  check_sym!(ctxt, sym, desc) ;
  let sys = match ctxt.get_sys(& sys) {
    Some(s) => s.clone(),
    None => {
      panic!("[check::check_prop] undefined system id in prop definition") ;
    },
  } ;
  // All symbols used in applications actually exist.
  for app_sym in body.apps.iter() {
    if ! app_defined(ctxt, app_sym) {
      return Err( UkCall(app_sym.clone(), sym, desc) )
    }
  } ;
  // Stateful var belong to state of system, non-stateful var exist.
  for var in body.vars.iter() {
    match * var.get() {
      // Non-stateful var exist.
      real::Var::Var(ref var_sym) => if ! var_defined(ctxt, var_sym) {
        return Err( UkVar(var.clone(), sym, desc) )
      },
      // Stateful var belong to state.
      // Next and current allowed.
      real::Var::SVar(ref var_sym, _) => if ! new_svar_in_state(
        var_sym, sys.state()
      ) {
        return Err( UkVar(var.clone(), sym, desc) )
      },
    }
  } ;
  ctxt.add_prop(
    Prop::mk(sym, sys, body.term)
  ) ;
  Ok(())
}

/** Checks that a symbol is in a list of local definitions. Returns a None if
it's not there, otherwise an option of a bool indicating if the term it is
bound to mentions next. */
fn is_sym_in_locals(
  sym: & Sym, locals: & [(Sym, Type, Term, bool)]
) -> Option<bool> {
  for &(ref local_sym, _, _, ref has_next) in locals.iter() {
    if sym == local_sym { return Some(* has_next) }
  } ;
  None
}

fn check_term_and_dep(
  term: & TermAndDep,
  ctxt: & Context, sym: & Sym, state: & Args,
  locals: & [ (Sym, Type, Term, bool) ],
  svar_allowed: bool, next_allowed: bool, desc: & 'static str
) -> Result<(), Error> {
  use term::real::Var::Var as NSVar ;
  use term::real::Var::SVar ;
  use term::State::* ;

  for var in term.vars.iter() {
    match * var.get() {
      NSVar(ref var_sym) => match is_sym_in_locals(var_sym, locals) {
        // No need to check if state vars are allowed.
        // There's locals so we're in a system.
        Some(is_next) => if is_next && ! next_allowed {
          panic!("next svar forbidden here in def of {}", var)
        },
        None => if var_defined(ctxt, var_sym) {
          return Err( UkVar(var.clone(), sym.clone(), desc) )
        },
      },
      SVar(ref var_sym, ref st) => if ! svar_allowed {
        panic!("svar fordibdden here {}", var)
      } else {
        if Next == * st && ! next_allowed {
          panic!("next svar forbidden here {}", var)
        } else {
          if ! new_svar_in_state(var_sym, state) {
            return Err( UkVar(var.clone(), sym.clone(), desc) )
          }
        }
      },
    }
  } ;

  for app_sym in term.apps.iter() {
    if ! app_defined(ctxt, app_sym) {
      return Err( UkCall(app_sym.clone(), sym.clone(), desc) )
    }
  } ;

  Ok(())
}

/** Checks that a system definition is legal. */
pub fn check_new_sys(
  ctxt: & mut Context, sym: Sym, state: Args,
  locals: Vec<(Sym, Type, TermAndDep)>,
  init: TermAndDep, trans: TermAndDep,
  sub_syss: Vec<(Sym, Vec<TermAndDep>)>
) -> Result<(), Error> {
  use term::State::* ;
  use std::iter::FromIterator ;

  let desc = super::sys_desc ;
  check_sym!(ctxt, sym, desc) ;

  println!("  checking locals") ;

  let mut tmp_locals = Vec::with_capacity(locals.len()) ;
  // All locals definitions make sense.
  for (local_sym, typ, def) in locals.into_iter() {
    let (term, apps, vars) = (def.term, def.apps, def.vars) ;
    let mut has_next = false ;
    // Applications mention existing symbols.
    for app_sym in apps.iter() {
      if ! app_defined(ctxt, app_sym) {
        return Err( UkCall(app_sym.clone(), sym, desc) )
      }
    } ;
    // Variables exist.
    for var in vars.iter() {
      match * var.get() {
        // Non-stateful var exists.
        real::Var::Var(ref var_sym) => match is_sym_in_locals(
          var_sym, & tmp_locals
        ) {
          Some(false) => (),
          Some(true) => has_next = true,
          None => if ! var_defined(ctxt, var_sym) {
            return Err( UkVar(var.clone(), sym, desc) )
          },
        },
        // Stateful var exists in state.
        real::Var::SVar(ref var_sym, ref st) => if ! new_svar_in_state(
          var_sym, & state
        ) {
          return Err( UkVar(var.clone(), sym, desc) )
        } else {
          match * st {
            Next => has_next = true,
            _ => (),
          }
        },
      }
    } ;
    tmp_locals.push( (local_sym, typ, term, has_next) )
  } ;

  println!("  checking init") ;

  let (init, init_vars, init_apps) = (init.term, init.vars, init.apps) ;
  // All symbols used in applications actually exist.
  for app_sym in init_apps.iter() {
    if ! app_defined(ctxt, app_sym) {
      return Err( UkCall(app_sym.clone(), sym, desc) )
    }
  } ;
  // Init:
  // * no next state vars
  // * current state vars exist in state
  // * non-stateful var exist.
  for var in init_vars.iter() {
    match * var.get() {
      // Non-stateful var exist.
      real::Var::Var(ref var_sym) => match is_sym_in_locals(
        var_sym, & tmp_locals
      ) {
        Some(false) => (),
        Some(true) => return Err( NxtInit(var_sym.clone(), sym) ),
        None => if ! var_defined(ctxt, var_sym) {
          return Err( UkVar(var.clone(), sym, desc) )
        },
      },
      // Next state variables are illegal.
      real::Var::SVar(ref var_sym, Next) => return Err(
        NxtInit(var_sym.clone(), sym)
      ),
      // Current stateful var belong to state.
      real::Var::SVar(ref var_sym, _) => if ! new_svar_in_state(
        var_sym, & state
      ) {
        return Err( UkVar(var.clone(), sym, desc) )
      },
    }
  } ;

  println!("  checking trans") ;

  let (trans, trans_vars, trans_apps) = (trans.term, trans.vars, trans.apps) ;
  // All symbols used in applications actually exist.
  for app_sym in trans_apps.iter() {
    if ! app_defined(ctxt, app_sym) {
      return Err( UkCall(app_sym.clone(), sym, desc) )
    }
  } ;
  // Trans:
  // * state vars exist in state
  // * non-stateful var exist.
  for var in trans_vars.iter() {
    match * var.get() {
      // Non-stateful var exist.
      real::Var::Var(ref var_sym) => match is_sym_in_locals(
        var_sym, & tmp_locals
      ) {
        Some(_) => (),
        None => if ! var_defined(ctxt, var_sym) {
          return Err( UkVar(var.clone(), sym, desc) )
        },
      },
      // Stateful var belong to state.
      real::Var::SVar(ref var_sym, _) => if ! new_svar_in_state(
        var_sym, & state
      ) {
        return Err( UkVar(var.clone(), sym, desc) )
      },
    }
  } ;

  println!("  checking calls") ;

  let mut calls = Vec::with_capacity(sub_syss.len()) ;
  // Sub systems exist and number of params matches their arity.
  for (sub_sym, params) in sub_syss.into_iter() {
    let sub_sys = match ctxt.get_sys(& sub_sym) {
      None => return Err( UkSysCall(sub_sym.clone(), sym) ),
      Some(ref sub_sys) => if sub_sys.state().args().len() != params.len() {
        return Err(
          IncSysCall(
            sub_sym.clone(), sub_sys.state().args().len(), sym, params.len()
          )
        )
      } else {
        (* sub_sys).clone()
      },
    } ;

    let mut nu_params = Vec::with_capacity(params.len()) ;
    for param in params.into_iter() {
      try!(
        check_term_and_dep(
          & param, ctxt, & sym, & state, & tmp_locals,
          true, false, desc
        )
      ) ;
      nu_params.push(param.term)
    } ;

    calls.push( (sub_sys, nu_params) )
  } ;

  // Actual locals vector.
  let locals = Vec::from_iter(
    tmp_locals.into_iter().map( |(sym, typ, term, _)| (sym, typ, term) )
  ) ;

  ctxt.add_sys(
    Sys::mk(sym, state, locals, init, trans, calls)
  ) ;

  Ok(())
}

/** Checks that a check is legal. */
pub fn check_check(
  ctxt: & Context, & (ref sys, ref props): & (Sym, Vec<Sym>)
) -> Result<(), Error> {
  let sys = match ctxt.get_sys(sys) {
    None => return Err( UkSys(sys.clone()) ),
    Some(sys) => sys,
  } ;
  for prop in props.iter() {
    let prop = match ctxt.get_prop(prop) {
      None => return Err( UkProp(prop.clone()) ),
      Some(prop) => prop,
    } ;
    if sys.sym() != prop.sys().sym() {
      return Err( IncPropState(sys.clone(), prop.clone()) )
    }
  } ;
  Ok(())
}