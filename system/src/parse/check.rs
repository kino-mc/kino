// Copyright 2015 Adrien Champion. See the COPYRIGHT file at the top-level
// directory of this distribution.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! Checks what has been parsed makes sense.
//!
//! See `parse::Context` for the description of the checks.

use std::fmt ;
use std::collections::HashSet ;

use term::{ Type, Sym, Var, Term, STerm } ;
use term::parsing::* ;
use term::real_term ;

use base::* ;
use super::{ Context, Atom, Res } ;

use self::CheckError::* ;
use self::CheckFailed::* ;
use parse::InternalParseError ;

/// Parse error.
#[derive(Debug)]
pub enum CheckError {
  /// Redefinition of identifier.
  Redef(Sym, & 'static str, & 'static str),
  /// State var in define-fun.
  SVarInDef(Var, Sym),
  /// Use of unknown symbol in application.
  UkCall(Sym, Sym, & 'static str),
  /// Use of unknown (state) variable.
  UkVar(Var, Sym, & 'static str),
  /// Use of unknown system identifier in verify or property.
  UkSys(Sym, Option<Sym>, & 'static str),
  /// Use of unknown prop identifier in verify.
  UkProp(Sym, Sym, & 'static str),
  /// Unknown atom in check with assumption.
  UkAtom(Sym, Sym, & 'static str),
  /// Illegal use of state variable.
  IllSVar(Var, Sym, & 'static str),
  /// Illegal use of next state variable.
  IllNxtSVar(Var, Sym, & 'static str),
  /// Inconsistent property in check.
  IncProp(::Prop, ::Sys, & 'static str),
  /// A next was found in a one-state property.
  NxtInProp1(Var, Sym, & 'static str),
  /// Illegal next state variable in init.
  NxtInit(Sym, Sym),
  /// Uknown system call in system definition.
  UkSysCall(Sym, Sym),
  /// Inconsistent arity of system call in system definition.
  IncSysCall(Sym, usize, Sym, usize),
  /// Type check error.
  TypeCheck(String),
  /// I/O error.
  Io(::std::io::Error),
}
impl fmt::Display for CheckError {
  fn fmt(& self, fmt: & mut fmt::Formatter) -> fmt::Result {
    use term::real_term::Var::* ;
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
      UkSys(ref sym, ref sym_opt, ref desc) => {
        let desc = match * sym_opt {
          None => desc.to_string(),
          Some(ref sym) => format!("{} {}", desc, sym),
        } ;
        write!(fmt, "unknown system {} in {}", sym, desc)
      },
      UkProp(ref prop_sym, ref sym, ref desc) => write!(
        fmt, "unknown property/relation {} in {} over {}", prop_sym, desc, sym
      ),
      UkAtom(ref atom_sym, ref sym, ref desc) => write!(
        fmt, "unknown literal {} in {} over {}", atom_sym, desc, sym
      ),
      IllSVar(ref var, ref sym, ref desc) => write!(
        fmt, "illegal use of state variable {} in {} {}", var, desc, sym
      ),
      IllNxtSVar(ref var, ref sym, ref desc) => write!(
        fmt, "illegal use of next state variable {} in {} {}", var, desc, sym
      ),
      IncProp(ref prop, ref sys, ref desc) => write!(
        fmt, "\
          property {} is over system {} \
          but {} is over system {}\
        ", prop.sym(), prop.sys().sym(), desc, sys.sym()
      ),
      NxtInProp1(ref var, ref sym, ref desc) => write!(
        fmt, "state variable {} is used as next in {} {}", 
        var.sym(), desc, sym
      ),
      NxtInit(ref var_sym, ref sym) => write!(
        fmt, "\
          init definition in system {} \
          uses state variable {} in next state\
        ", sym, var_sym
      ),
      UkSysCall(ref sub_sym, ref sym) => write!(
        fmt, "unknown system call to {} in {} {}",
        sub_sym, sym, super::sys_desc
      ),
      IncSysCall(ref sub_sym, ref arity, ref sym, ref arg_count) => write!(
        fmt, "\
          illegal system call to {} in {} {}: \
          {} parameters given but {} has arity {}\
        ", sub_sym, super::sys_desc, sym, arg_count, sub_sym, arity
      ),
      TypeCheck(ref s) => write!(fmt, "{}", s),
      Io(ref e) => write!(fmt, "i/o error \"{}\"", e),
    }
  }
}

/// Checks that an identifier is unused.
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

/// Checks that an identifier is unused.
macro_rules! new_check_sym {
  ($ctxt:expr, $sym:expr) => (
    match $ctxt.sym_unused(& $sym.val) {
      None => (),
      Some(_) => return Err(
        InternalParseError::mk(
          $sym.span, format!("redefining symbol `{}`", $sym.val),
          vec![]
        )
      ),
    }
  )
}

/// Type checks a term.
macro_rules! type_check {
  (
    $ctxt:expr, $term:expr, $ty:expr,
    state: $state:expr, $desc:expr, $( $fmt:tt )+
  ) => (
    type_check!(internal
      $ctxt, $term, $ty, Some($state), None, $desc, $( $fmt )+
    )
  ) ;
  (
    $ctxt:expr, $term:expr, $ty:expr,
    sig: $sig:expr, $desc:expr, $( $fmt:tt )+
  ) => (
    type_check!(internal
      $ctxt, $term, $ty, None, Some($sig), $desc, $( $fmt )+
    )
  ) ;
  (
    internal $ctxt:expr, $term:expr, $ty:expr,
    $state:expr, $sig:expr, $desc: expr, $t:ident => $( $fmt:tt )+
  ) => (
    match ::type_check::type_check(
      $ctxt, & $term, $state, $sig
    ) {
      Ok($t) => if $t != $ty {
        return Err(
          TypeCheck(
            format!(
              "{}\n{}", $desc, format!( $( $fmt )+ )
            )
          )
        )
      },
      Err(s) => return Err(
        TypeCheck( format!("{}\n{}", $desc, s) )
      ),
    }
  ) ;
}

/// Type checks a term.
macro_rules! new_type_check {
  (
    $ctxt:expr, $term:expr, $ty:expr,
    state: $state:expr, $span:expr, $( $fmt:tt )+
  ) => (
    new_type_check!(internal
      $ctxt, $term, $ty, Some($state), None, $span, $( $fmt )+
    )
  ) ;
  (
    $ctxt:expr, $term:expr, $ty:expr,
    sig: $sig:expr, $span:expr, $( $fmt:tt )+
  ) => (
    new_type_check!(internal
      $ctxt, $term, $ty, None, Some($sig), $span, $( $fmt )+
    )
  ) ;
  (
    internal $ctxt:expr, $term:expr, $ty:expr,
    $state:expr, $sig:expr, $span:expr, $t:ident => $( $fmt:tt )+
  ) => (
    match ::type_check::type_check(
      $ctxt, & $term, $state, $sig
    ) {
      Ok($t) => if $t != $ty.val {
        return Err(
          InternalParseError::mk(
            $ty.span, format!($($fmt)+), vec![]
          )
        )
      },
      Err(s) => return Err(
        InternalParseError::mk(
          $span, s, vec![]
        )
      ),
    }
  ) ;
}

/// Checks that a variable is defined. That is, looks for a function symbol
/// declaration/definition for the variable's symbol with arity zero.
fn var_defined(
  ctxt: & Context, sym: & Sym
) -> Option<::Callable> {
  use base::Callable::* ;
  match ctxt.get_callable(sym) {
    None => None,
    Some(fun) => match * * fun {
      Dec(ref f) => if f.sig().len() == 0 { Some(fun.clone()) } else { None },
      Def(ref f) => if f.args().len() == 0 { Some(fun.clone()) } else { None },
    },
  }
}

/// Checks that an application is defined. That is, looks for a function symbol
/// declaration/definition for a symbol with arity greater than zero.
fn app_defined(
  ctxt: & Context, sym: & Sym
) -> Option<::Callable> {
  use base::Callable::* ;
  match ctxt.get_callable(sym) {
    None => None,
    Some(fun) => match * * fun {
      Dec(ref f) => if f.sig().len() > 0 { Some(fun.clone()) } else { None },
      Def(ref f) => if f.args().len() > 0 { Some(fun.clone()) } else { None },
    },
  }
}

/// Checks that a state variables belongs to a state.
fn svar_in_state(
  svar: & Sym, state: & Args
) -> bool {
  for & (ref s, _) in state.args().iter() {
    if s.get() == svar { return true }
  } ;
  false
}

/// Checks that a symbol is in a list of local definitions. Returns an option
/// of the relevant binding if it is, `None` otherwise.
fn is_sym_in_locals(
  sym: & Sym, locals: & [(Sym, Type, Term)]
) -> Option<(Sym, Term)> {
  for & (ref local_sym, _, ref term) in locals.iter() {
    if sym == local_sym { return Some( (local_sym.clone(), term.clone()) ) }
  } ;
  None
}

/// Checks that a function declaration is legal.
pub fn check_fun_dec(
  ctxt: & Context, sym: Spnd<Sym>, sig: Sig, typ: Spnd<Type>
) -> Result<Callable, InternalParseError> {
  new_check_sym!(ctxt, sym) ;
  match ctxt.factory().set_fun_type(sym.get().clone(), * typ.get()) {
    Ok(()) => (),
    Err(e) => return Err(
      InternalParseError::mk(
        sym.span, format!("{}", e), vec![]
      )
    ),
  } ;
  Ok( Callable::Dec( Uf::mk(sym, sig, typ) ) )
}

/// Checks that a function definition is legal.
pub fn check_fun_def(
  ctxt: & Context, sym: Spnd<Sym>, args: Args,
  typ: Spnd<Type>, body: TermAndDep
) -> Result<Callable, InternalParseError> {
  new_check_sym!(ctxt, sym) ;

  let mut calls = CallSet::empty() ;

  // All symbols used in applications actually exist.
  for call_sym in body.apps.iter() {
    match app_defined(ctxt, call_sym) {
      None => return Err(
        InternalParseError::mk(
          sym.span,
          format!(
            "application of unknown function symbol `{}` in body", call_sym
          ),
          vec![]
        )
      ),
      Some(f) => {
        // Don't care if it was already there.
        calls.insert(f) ;
      },
    }
  } ;
  // No stateful var, all non-stateful vars exist.
  for var in body.vars.iter() {
    match * var.get() {
      real_term::Var::Var(ref var_sym) => {
        match var_defined(ctxt, var_sym) {
          None => {
            let mut exists = false ;
            for & (ref dsym, _) in args.args() {
              if dsym.get() == var_sym { exists = true }
            } ;
            if ! exists {
              return Err(
                InternalParseError::mk(
                  sym.span,
                  format!(
                    "unknown constant function symbol `{}` in body", var_sym
                  ),
                  vec![]
                )
              )
            }
          },
          Some(fun) => { calls.insert(fun) ; },
        }
      },
      _ => return Err(
        InternalParseError::mk(
          sym.span,
          format!("illegal state variable `{}` in body", var),
          vec![]
        )
      ),
    }
  } ;

  new_type_check!(
    ctxt, body.term, typ, sig: args.args(), sym.span,
    t => "body of function is inconsistent with return type\n  \
      expected {}, got {}", typ.val, t
  ) ;

  match ctxt.factory().set_fun_type(
    sym.get().clone(), typ.get().clone()
  ) {
    Ok(()) => (),
    Err(e) => return Err(
      InternalParseError::mk(
        sym.span, format!("{}", e), vec![]
      )
    ),
  } ;

  Ok(
    Callable::Def( Fun::mk(sym, args, typ, body.term, calls) )
  )
}

enum CheckFailed {
  HasNext(Var),
  HasSVar(Var),
  UnknownVar(Var),
  UnknownSVar(Var),
  UnknownCall(Sym),
}

/// Checks everything in a term is well defined.
///
/// Returns a `Result` of the bindings from the `locals` necessary for the
/// term to make sense.
fn check_term_and_dep(
  ctxt: & Context,
  term: & TermAndDep,
  locals: & [ (Sym, Type, Term) ],
  state: & Args,
  svar_allowed: bool,
  next_allowed: bool,
  calls: & mut CallSet
) -> Result<HashSet<(Sym, Term)>, CheckFailed> {
  use term::real_term::Var::Var as NSVar ;
  use term::real_term::Var::SVar ;
  use term::State::* ;

  let mut bindings = HashSet::with_capacity(locals.len()) ;

  for var in term.vars.iter() {
    match * var.get() {
      NSVar(ref var_sym) => match is_sym_in_locals(var_sym, locals) {
        Some( (sym, term) ) => {
          bindings.insert( (sym, term) ) ; ()
        },
        None => match var_defined(ctxt, var_sym) {
          None => return Err( UnknownVar(var.clone()) ),
          Some(fun) => { calls.insert(fun) ; () },
        },
      },
      SVar(ref var_sym, ref st) => if ! svar_allowed {
        return Err( HasSVar(var.clone()) )
      } else {
        if Next == * st && ! next_allowed {
          return Err( HasNext(var.clone()) )
        } else {
          if ! svar_in_state(var_sym, state) {
            return Err( UnknownSVar(var.clone()) )
          }
        }
      },
    }
  } ;

  for app_sym in term.apps.iter() {
    match app_defined(ctxt, app_sym) {
      None => return Err( UnknownCall(app_sym.clone()) ),
      Some(fun) => {
        // Don't care if it was already there.
        calls.insert(fun) ;
      },
    }
  } ;

  Ok(bindings)
}

/// Checks that a proposition definition is legal.
pub fn check_prop(
  ctxt: & Context, sym: Spnd<Sym>, spnd_sys: Spnd<Sym>, body: TermAndDep
) -> Result<Prop, InternalParseError> {
  use term::State::Curr ;
  use term::UnTermOps ;
  new_check_sym!(ctxt, sym) ;

  let sys = match ctxt.get_sys( & spnd_sys ) {
    Some(s) => s.clone(),
    None => {
      return Err(
        InternalParseError::mk(
          spnd_sys.span, "unknown system".into(), vec![]
        )
      )
    },
  } ;

  let mut calls = CallSet::empty() ;

  // All symbols used in applications actually exist.
  for app_sym in body.apps.iter() {
    match app_defined(ctxt, app_sym) {
      None => return Err(
        InternalParseError::mk(
          sym.span,
          format!(
            "application of unknown function symbol `{}`in body", app_sym
          ),
          vec![]
        )
      ),
      Some(fun) => { calls.insert(fun) ; },
    }
  } ;
  // Stateful var belong to state of system, non-stateful var exist.
  for var in body.vars.iter() {
    match * var.get() {
      // Non-stateful var exist.
      real_term::Var::Var(ref var_sym) => match var_defined(ctxt, var_sym) {
        None => return Err(
          InternalParseError::mk(
            sym.span,
            format!("unknown constant function symbol `{}` in body", var_sym),
            vec![]
          )
        ),
        Some(fun) => { calls.insert(fun) ; },
      },
      // Stateful var belong to state.
      // Next forbidden.
      real_term::Var::SVar(ref var_sym, Curr) => if ! svar_in_state(
        var_sym, sys.state()
      ) {
        return Err(
          InternalParseError::mk(
            sym.span.clone(),
            format!("unknown state variable `{}` in body", var_sym),
            vec![
              (spnd_sys.span, "state variables must belong \
                to the system referenced here".into()
              )
            ]
          )
        )
      },
      real_term::Var::SVar(_, ::term::State::Next) => return Err(
        InternalParseError::mk(
          sym.span.clone(),
          format!(
            "illegal state variable in next state `{}` in body", var.get()
          ),
          vec![
            (spnd_sys.span, "only state variables of this system in the \
              current state are allowed in properties\n\
              Use `define-rel` instead to allow state variables in the next \
              state".into()
            )
          ]
        )
      ),
    }
  } ;

  new_type_check!(
    ctxt, body.term, Spnd::mk(
      Type::Bool, sym.span.clone()
    ), state: sys.state().args(),
    sym.span,
    t => "body of property should have type Bool, got {}", t
  ) ;

  // Unwrap cannot fail, we just checked no svar was used as next.
  let nxt = ctxt.factory().bump(body.term.clone()).unwrap() ;
  let body = STerm::One(body.term, nxt) ;

  Ok(
    Prop::mk(sym.clone(), sys.clone(), body, calls)
  )
}

/// Checks that a relation definition is legal.
pub fn check_rel(
  ctxt: & Context, sym: Spnd<Sym>, spnd_sys: Spnd<Sym>, body: TermAndDep
) -> Result<Prop, InternalParseError> {
  new_check_sym!(ctxt, sym) ;

  let sys = match ctxt.get_sys(& spnd_sys) {
    Some(s) => s.clone(),
    None => return Err(
      InternalParseError::mk(
        spnd_sys.span, "unknown system".into(), vec![]
      )
    ),
  } ;

  let mut calls = CallSet::empty() ;

  // All symbols used in applications actually exist.
  for app_sym in body.apps.iter() {
    match app_defined(ctxt, app_sym) {
      None => return Err(
        InternalParseError::mk(
          sym.span,
          format!(
            "application of unknown function symbol `{}`in body", app_sym
          ),
          vec![]
        )
      ),
      Some(fun) => { calls.insert(fun) ; },
    }
  } ;
  // Stateful var belong to state of system, non-stateful var exist.
  for var in body.vars.iter() {
    match * var.get() {
      // Non-stateful var exist.
      real_term::Var::Var(ref var_sym) => match var_defined(ctxt, var_sym) {
        None => return Err(
          InternalParseError::mk(
            sym.span,
            format!("unknown constant function symbol `{}` in body", var_sym),
            vec![]
          )
        ),
        Some(fun) => { calls.insert(fun) ; },
      },
      // Stateful var belong to state.
      // Next forbidden.
      real_term::Var::SVar(ref var_sym, _) => if ! svar_in_state(
        var_sym, sys.state()
      ) {
        return Err(
          InternalParseError::mk(
            sym.span.clone(),
            format!("unknown state variable `{}` in body", var_sym),
            vec![
              (spnd_sys.span, "state variables must belong \
                to the system referenced here".into()
              )
            ]
          )
        )
      },
    }
  } ;

  new_type_check!(
    ctxt, body.term, Spnd::mk(
      Type::Bool, sym.span.clone()
    ), state: sys.state().args(), sym.span.clone(),
    t => "body of relation should have type Bool, got {}", t
  ) ;

  let body = STerm::Two(body.term) ;
  Ok(
    Prop::mk(sym.clone(), sys.clone(), body, calls)
  )
}

macro_rules! sys_try {
  ($check:expr, $ctxt:expr, $term:expr, $sym:expr, $span:expr, $blah:expr) => (
    match $check {
      Ok( bindings ) => Ok(
        $ctxt.factory().let_b(
          Vec::from_iter( bindings.into_iter() ), $term
        )
      ),
      Err( HasNext(var) ) => Err(
        InternalParseError::mk(
          $span, format!(
            "illegal next state variable {}", $blah
          ), vec![]
        )
      ),
      Err( HasSVar(var) ) => Err(
        InternalParseError::mk(
          $span, format!(
            "illegal state variable {}", $blah
          ), vec![]
        )
      ),
      Err( UnknownVar(var) ) => Err(
        InternalParseError::mk(
          $span, format!(
            "unknown constant function symbol {}", $blah
          ), vec![]
        )
      ),
      Err( UnknownSVar(var) ) => Err(
        InternalParseError::mk(
          $span, format!(
            "unknown state variable {}", $blah
          ), vec![]
        )
      ),
      Err( UnknownCall(s) ) => Err(
        InternalParseError::mk(
          $span, format!(
            "application of unknown function symbol {}", $blah
          ), vec![]
        )
      ),
    }
  )
}

/// Checks that a system definition is legal.
pub fn check_sys(
  ctxt: & Context, sym: Spnd<Sym>, state: Args,
  locals: Vec<(Spnd<Sym>, Spnd<Type>, TermAndDep)>,
  init: TermAndDep, trans: TermAndDep,
  sub_syss: Vec<(Spnd<Sym>, Vec<TermAndDep>)>
) -> Result<Sys, InternalParseError> {
  use term::State::* ;
  use term::{
    SymMaker, VarMaker, AppMaker, UnTermOps, BindMaker
  } ;
  use std::iter::{ Extend, FromIterator } ;

  new_check_sym!(ctxt, sym) ;

  let mut calls = CallSet::empty() ;

  let mut local_vars = Vec::with_capacity(locals.len()) ;
  // All locals definitions make sense.
  for (local_sym, typ, term) in locals.into_iter() {
    // Check local definition. No next allowed.
    let term = try!(
      sys_try!(
        check_term_and_dep(
          ctxt, & term, & local_vars, & state, true, false, & mut calls
        ), ctxt, term.term, sym.get().clone(), sym.span.clone(),
        "in local variable"
      )
    ) ;

    new_type_check!(
      ctxt, term, typ.clone(), state: state.args(), sym.span.clone(),
      t =>
        "local variable {} was declared with type {}, got {}",
        local_sym, typ, t
    ) ;

    local_vars.push( (local_sym.val, typ.val, term) )
  } ;

  // Init:
  // * no next state vars
  // * current state vars exist in state
  // * non-stateful var exist.
  new_type_check!(
    ctxt, init.term, Spnd::mk(
      Type::Bool, sym.span.clone()
    ), state: state.args(), sym.span.clone(),
    t => "init predicate should have type Bool, got {}", t
  ) ;
  let init = try!(
    sys_try!(
      check_term_and_dep(
        ctxt, & init, & local_vars, & state, true, false, & mut calls
      ), ctxt, init.term, sym.get().clone(), sym.span.clone(),
        "in init predicate"
    )
  ) ;

  // Trans:
  // * state vars exist in state
  // * non-stateful var exist.
  new_type_check!(
    ctxt, trans.term, Spnd::mk(
      Type::Bool, sym.span.clone()
    ), state: state.args(), sym.span,
    t => "trans predicate should have type Bool, got {}", t
  ) ;
  let trans = try!(
    sys_try!(
      check_term_and_dep(
        ctxt, & trans, & local_vars, & state, true, true, & mut calls
      ), ctxt, trans.term, sym.get().clone(), sym.span.clone(),
      "in trans predicate"
    )
  ) ;

  let mut subsys = Vec::with_capacity(sub_syss.len()) ;
  // Sub systems exist and number of params matches their arity.
  for (sub_sym, params) in sub_syss.into_iter() {
    let sub_sys = match ctxt.get_sys(sub_sym.get()) {
      None => return Err(
        InternalParseError::mk(
          sub_sym.span, "composition with unknown system".into(), vec![]
        )
      ),
      Some(ref sub_sys) => if sub_sys.state().args().len() != params.len() {
        return Err(
          InternalParseError::mk(
            sub_sym.span, format!(
              "state arity mismatch, expected {} arguments but got {}",
              sub_sys.state().args().len(), params.len()
            ), vec![]
          )
        )
      } else {
        (* sub_sys).clone()
      },
    } ;

    let mut nu_params = Vec::with_capacity(params.len()) ;
    for param in params.into_iter() {
      let term = try!(
        sys_try!(
          check_term_and_dep(
            ctxt, & param, & local_vars, & state, true, false, & mut calls
          ), ctxt, param.term, sym.get().clone(), sym.span.clone(),
          "in argument for system composition"
        ).map_err(
          |mut e| {
            e.notes.push(
              (sub_sym.span.clone(), "in this system composition".into())
            ) ;
            e
          }
        )
      ) ;
      nu_params.push(term)
    } ;

    for call in sub_sys.calls().get() {
      calls.insert(call.clone()) ;
    } ;

    subsys.push( (sub_sys, nu_params) )
  } ;

  // let mut init_binding = Vec::with_capacity(local_vars.len()) ;
  // let mut trans_binding = Vec::with_capacity(local_vars.len()) ;

  // for & (ref sym, _, ref t) in local_vars.iter() {
  //   init_binding.push( (sym.clone(), i.clone()) ) ;
  //   trans_binding.push( (sym.clone(), t.clone()) )
  // } ;

  let mut init_state = Vec::with_capacity(state.len()) ;
  let mut trans_state = Vec::with_capacity(2 * state.len()) ;
  let mut tmp_state = Vec::with_capacity(state.len()) ;
  {
    let f = ctxt.factory() ;
    for & (ref sym, ref typ) in state.args() {
      let var: Var = f.svar(sym.get().clone(), Curr) ;
      init_state.push(
        (var.clone(), typ.get().clone())
      ) ;
      trans_state.push(
        (var, typ.get().clone())
      ) ;
      let nxt: Var = f.svar(sym.get().clone(), Next) ;
      tmp_state.push(
        (nxt, typ.get().clone())
      ) ;
    }
  }
  trans_state.extend(tmp_state) ;

  let init_sym = ctxt.factory().sym(
    format!("init[{}]", sym.get().sym())
  ) ;
  let trans_sym = ctxt.factory().sym(
    format!("trans[{}]", sym.get().sym())
  ) ;

  let mut init_conjs = Vec::with_capacity(subsys.len() + 1) ;
  init_conjs.push(init) ;
  let mut trans_conjs = Vec::with_capacity(subsys.len() + 1) ;
  trans_conjs.push(trans) ;
  for & (ref sub, ref params) in subsys.iter() {
    init_conjs.push(
      ctxt.factory().app(sub.init().0.clone(), params.clone())
    ) ;
    let mut trans_params = params.clone() ;
    for term in params {
      trans_params.push( ctxt.factory().bump(term).unwrap() )
    } ;
    trans_conjs.push(
      ctxt.factory().app(sub.trans().0.clone(), trans_params)
    )
  } ;

  let init = ctxt.factory().and(init_conjs) ;
  let trans = ctxt.factory().and(trans_conjs) ;

  let mut init_params = Vec::with_capacity(init_state.len()) ;
  for & (ref var, _) in init_state.iter() {
    init_params.push(
      ctxt.factory().mk_var(var.clone())
    )
  } ;
  let mut trans_params = Vec::with_capacity(trans_state.len()) ;
  for & (ref var, _) in trans_state.iter() {
    trans_params.push(
      ctxt.factory().mk_var(var.clone())
    )
  } ;
  let (init_term, trans_term) = (
    ctxt.factory().app(init_sym.clone(), init_params),
    ctxt.factory().app(trans_sym.clone(), trans_params)
  ) ;

  for & (ref v_sym, ref typ) in state.args() {
    let svar = ctxt.factory().svar(v_sym.get().clone(), Curr) ;
    match ctxt.factory().set_var_type(
      Some( sym.get().clone() ), svar, typ.get().clone()
    ) {
      Ok(()) => (),
      Err(e) => return Err(
        InternalParseError::mk(
          sym.span, format!("{}", e), vec![]
        )
      ),
    }
  }

  Ok(
    Sys::mk(
      sym, state, local_vars,
      (init_sym, init_state, init, init_term),
      (trans_sym, trans_state, trans, trans_term),
      subsys, calls,
    )
  )
}

/// Checks that a check is legal.
pub fn check_check(
  ctxt: & Context, sym: Spnd<Sym>,
  props: Vec< Spnd<Sym> >, atoms: Option<Vec<Atom>>
) -> Result<Res, CheckError> {
  let desc = if atoms.is_none() {
    super::check_desc
  } else {
    super::check_ass_desc
  } ;

  let sys = match ctxt.get_sys(& sym) {
    None => return Err( UkSys(sym.get().clone(), None, desc) ),
    Some(sys) => (* sys).clone(),
  } ;

  let mut real_props = Vec::with_capacity(props.len()) ;
  for prop in props.iter() {
    let prop = match ctxt.get_prop(prop.get()) {
      None => return Err(
        UkProp(prop.get().clone(), sym.get().clone(), desc)
      ),
      Some(prop) => (* prop).0.clone(),
    } ;
    if sys.sym() != prop.sys().sym() {
      return Err( IncProp(prop.clone(), sys.clone(), desc) )
    } else {
      real_props.push(prop)
    }
  } ;

  match atoms {

    None => Ok( Res::Check(sys, real_props) ),

    Some(atoms) => {
      let mut nu_atoms = Vec::with_capacity(atoms.len()) ;
      for atom in atoms.into_iter() {
        match var_defined(ctxt, atom.sym()) {
          None => return Err(
            UkAtom(atom.sym().get().clone(), sym.get().clone(), desc)
          ),
          Some(_) => (),
        } ;
        nu_atoms.push( atom.into_var(ctxt.factory()) )
      } ;
      Ok( Res::CheckAss(sys, real_props, nu_atoms) )
    }
  }
}