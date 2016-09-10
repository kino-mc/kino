#![deny(missing_docs)]
// Copyright 2016 Adrien Champion. See the COPYRIGHT file at the top-level
// directory of this distribution.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! Convenience traits and structures for unrolling a system and handling
//! properties.

extern crate term ;
extern crate system as sys ;
#[macro_use]
extern crate common ;

use std::collections::{ HashSet, HashMap } ;
use std::hash::Hash ;
use std::cmp::Eq ;
use std::fmt::Display ;
use std::iter::{ Iterator, IntoIterator } ;

use term::{
  Type, Sym, Term, Model,
  Offset, Offset2, STerm, STermSet, real_term
} ;
use term::smt::* ;
use term::tmp::* ;

use sys::{ Prop, Sys, Callable } ;

use common::{ Res, SolverTrait } ;

/// Manages some properties.
pub type PropManager = TermManager<Sym> ;
/// Manages some invariants.
pub type InvManager = TermManager<STerm> ;

/// Associates a key and a description to some type.
#[derive(Clone)]
pub struct Opt<T: Clone> {
  /// The key.
  pub key: (& 'static str, String),
  /// The description.
  pub bla: Vec<String>,
  /// The value.
  pub val: T,
}
impl<T: Clone> Opt<T> {
  /// Creates a new option.
  pub fn mk(
    key: (& 'static str, String), bla: Vec<String>, val: T
  ) -> Self {
    Opt { key: key, bla: bla, val: val }
  }
  /// Append the lines describing an `Opt` to some String.
  pub fn append(& self, s: & mut String, pref: & str) {
    s.push_str(
      & format!("{}{}{}", pref, self.key.0, self.key.1)
    ) ;
    for line in self.bla.iter() {
      s.push_str( & format!("\n{}   {}", pref, line) )
    }
  }
}

/// Defines the init and trans predicates of a system.
fn define<'a, S: SolverTrait<'a>>(
  sys: & sys::Sys, solver: & mut S, o: & Offset2
) -> UnitSmtRes {
  let init = sys.init() ;
  try!(
    solver.define_fun(
      & init.0,
      & init.1,
      & Type::Bool,
      & init.2,
      o
    )
  ) ;
  let trans = sys.trans() ;
  solver.define_fun(
    & trans.0,
    & trans.1,
    & Type::Bool,
    & trans.2,
    o
  )
}


/// Can unroll a system.
///
/// An `Unroller` does **not** handle the unrolling depth. This is up to the
/// client, as many operations depend on whether the unrolling is forward or
/// backward.
///
/// In particular, **adding new invariants does not assert them "from `0` to
/// `k`"**. This depends on the direction of unrolling and is up to the client.
///
/// Unrolling however asserts invariants using one of these strategies:
///
/// - [`unroll`](struct.Unroller.html#method.unroll)
/// - [`unroll_init`](struct.Unroller.html#method.unroll_init)
/// - [`unroll_bak`](struct.Unroller.html#method.unroll_bak)
pub struct Unroller<S> {
  /// The system to unroll.
  sys: Sys,
  /// The solver used to unroll the system.
  solver: S,
  /// The invariants known on the system.
  invs: STermSet,
  // /// Offset of the beginning of the trace.
  // beg_k: Offset2,
  // /// Offset of the end of the trace.
  // end_k: Offset2,
  /// Actlit factory.
  act_factory: ActlitFactory,
}

impl<
  'a, S: SolverTrait<'a>
> Unroller<S> {
  /// Creates an unroller from a system.
  ///
  /// Declares everything needed at `0`.
  #[inline]
  pub fn mk(sys: & Sys, props: & [Prop], solver: S) -> Res<Self> {
    let mut unroller = Unroller {
      sys: sys.clone(),
      solver: solver,
      invs: STermSet::with_capacity(107),
      // beg_k: Offset2::init(),
      // end_k: Offset2::init().pre(),
      act_factory: ActlitFactory::mk(),
    } ;
    try_str!(
      unroller.defclare_funs(props), "during function defclaration"
    ) ;
    Ok(unroller)
  }

  // /// Creates an unroller that unrolls backwards.
  // #[inline]
  // pub fn mk_rev(sys: & Sys, solver: S) -> Self {
  //   let mut res = Self::mk(sys, solver) ;
  //   res.beg_k = res.beg_k.rev() ;
  //   res.end_k = res.end_k.rev() ;
  //   res
  // }

  /// Accessor for the system.
  #[inline]
  pub fn sys(& self) -> & Sys { & self.sys }
  /// Accessor for the solver.
  #[inline]
  pub fn solver(& mut self) -> & mut S { & mut self.solver }
  /// Accessor for the invariants.
  #[inline]
  pub fn invs(& self) -> & STermSet { & self.invs }

  /// Creates and declares a fresh activation literal.
  #[inline]
  pub fn fresh_actlit(& mut self) -> Res<Actlit> {
    let actlit = self.act_factory.mk_fresh() ;
    try_str!(
      actlit.declare( & mut self.solver ),
      "[Unroller::fresh_actlit] error at SMT level in declaration"
    ) ;
    Ok( actlit )
  }

  /// Deactivates an activation literal.
  #[inline]
  pub fn deactivate(& mut self, actlit: Actlit) -> Res<()> {
    Ok(
      try_str!(
        actlit.deactivate(& mut self.solver),
        "[Unroller::deactivate] error at SMT level"
      )
    )
  }

  /// Performs a check sat.
  #[inline]
  pub fn check_sat(& mut self) -> Res<bool> {
    Ok(
      try_str!(
        self.solver.check_sat(),
        "[Unroller::check_sat] error at SMT level"
      )
    )
  }

  /// Performs a check sat assuming.
  #[inline]
  pub fn check_sat_assuming(
    & mut self, idents: & [String]
  ) -> Res<bool> {
    Ok(
      try_str!(
        self.solver.check_sat_assuming(idents, & ()),
        "[Unroller::check_sat_assuming] error at SMT level"
      )
    )
  }

  /// Asserts something.
  #[inline]
  pub fn assert< Expr: Expr2Smt<Offset2> >(
    & mut self, expr: & Expr, info: & Offset2
  ) -> Res<()> {
    Ok(
      try_str!(
        self.solver.assert(expr, info),
        "[Unroller::assert] error at SMT level"
      )
    )
  }

  fn defclare_funs_iter<'b, T: Iterator<Item = & 'b Callable>>(
    solver: & mut S, funs: T, offset: & Offset2,
    known: & mut HashSet<Sym>,
    rest: & mut HashSet<& 'b Callable>
  ) -> UnitSmtRes {
    use sys::real_sys::Callable::* ;
    for fun in funs {
      // println!("{}, known:", fun.sym()) ;
      // for known in known.iter() { println!("  {}", known) }
      // println!("defining {}", fun.sym()) ;
      match * * fun {
        Dec(ref fun_dec) => if ! known.contains(fun_dec.sym()) {
          known.insert( fun_dec.sym().clone() ) ;
          try!(
            solver.declare_fun(
              fun_dec.sym(), fun_dec.sig(), fun_dec.typ(), offset
            )
          )
        },
        Def(ref fun_def) => if ! known.contains(fun_def.sym()) {
          let declare = {
            let mut ok = true ;
            for sub in fun_def.calls().get() {
              if ! known.contains(sub.sym()) {
                ok = false ;
                break
              }
            }
            ok
          } ;
          if declare {
            known.insert( fun_def.sym().clone() ) ;
            try!(
              solver.define_fun(
                fun_def.sym(), fun_def.args(),
                fun_def.typ(), fun_def.body(), offset
              )
            )
          } else {
            rest.insert(fun) ; ()
          }
        },
      }
    } ;
    Ok(())
  }

  fn defclare_sys_iter<'b, U: 'b, T: Iterator<Item = & 'b (Sys, U)>>(
    solver: & mut S, syss: T, offset: & Offset2,
    known: & mut HashSet<Sym>,
    rest: & mut Vec< (Sys, ()) >
  ) -> UnitSmtRes {
    for & (ref sys, _) in syss {
      if ! known.contains( sys.sym() ) {
        let declare = {
          let mut ok = true ;
          for &(ref sys, _) in sys.subsys() {
            if ! known.contains(sys.sym()) {
              ok = false ;
              break
            }
          }
          ok
        } ;
        if declare {
          known.insert( sys.sym().clone() ) ;
          try!( define(sys, solver, & offset) )
        } else {
          rest.push( (sys.clone(), ()) ) ; ()
        }
      }
    }
    Ok(())
  }

  /// Declares/defines UFs, functions, and system init/trans predicates.
  pub fn defclare_funs(& mut self, props: & [ Prop ]) -> UnitSmtRes {
    // Will not really be used.
    let offset = Offset2::init() ;

    let mut known = HashSet::with_capacity(7) ;
    let mut rest = HashSet::with_capacity(7) ;
    // Declaring UFs and defining functions.
    // println!("declaring UFs, defining funs") ;
    try!(
      Self::defclare_funs_iter(
        & mut self.solver, self.sys.calls().get().iter(),
        & offset, & mut known, & mut rest
      )
    ) ;
    while ! rest.is_empty() {
      use std::mem::swap ;
      let mut calls = HashSet::with_capacity(7) ;
      swap(& mut calls, & mut rest) ;
      try!(
        Self::defclare_funs_iter(
          & mut self.solver, calls.into_iter(),
          & offset, & mut known, & mut rest
        )
      )
    }

    for prop in props.iter() {
      try!(
        Self::defclare_funs_iter(
          & mut self.solver, prop.calls().get().into_iter(),
          & offset, & mut known, & mut rest
        )
      )
    }

    while ! rest.is_empty() {
      use std::mem::swap ;
      let mut calls = HashSet::with_capacity(7) ;
      swap(& mut calls, & mut rest) ;
      try!(
        Self::defclare_funs_iter(
          & mut self.solver, calls.into_iter(),
          & offset, & mut known, & mut rest
        )
      )
    }

    // Defining sub systems.
    // println!("defining sub systems") ;
    let mut known = HashSet::with_capacity(7) ;
    let mut rest = Vec::with_capacity(7) ;
    try!(
      Self::defclare_sys_iter(
        & mut self.solver, self.sys.subsys().iter(),
        & offset, & mut known, & mut rest
      )
    ) ;
    while ! rest.is_empty() {
      use std::mem::swap ;
      let mut syss = Vec::with_capacity(7) ;
      swap(& mut syss, & mut rest) ;
      try!(
        Self::defclare_sys_iter(
          & mut self.solver, syss.iter(),
          & offset, & mut known, & mut rest
        )
      ) ;
    }

    // Define current system.
    // println!("defining top system") ;
    define(& self.sys, & mut self.solver, & offset)
  }

  /// Declares state variables at some offset.
  #[inline]
  pub fn declare_svars(& mut self, o: & Offset) -> UnitSmtRes {
    for & (ref var, ref typ) in self.sys.init().1.iter() {
      try!(
        self.solver.declare_fun(var, & vec![], typ, o)
      )
    } ;
    Ok(())
  }

  /// Asserts one state invariants at `off.curr()`.
  #[inline]
  pub fn assert_os_invs(& mut self, off: & Offset2) -> Res<()> {
    for inv in self.invs.iter() {
      if let STerm::One(ref curr, _) = * inv {
        try!(
          self.solver.assert(curr, off).map_err(
            |err| format!(
              "[Unroller::assert_os_invs] \
              while asserting one-state inv {} at {}\n{}", curr, off, err
            )
          )
        )
      }
    }
    Ok(())
  }

  /// Asserts the init predicate. **Declares** state variables in the current
  /// offset.
  #[inline]
  pub fn assert_init(& mut self, o: & Offset2) -> UnitSmtRes {
    try!(
      self.declare_svars( o.curr() )
    ) ;
    self.solver.assert( self.sys.init_term(), o )
  }

  /// Unrolls the transition relation once. **Declares** state variables in
  /// the next offset if the offset is not reversed, in the current offset
  /// otherwise (for backward unrolling).
  fn just_unroll(& mut self, o: & Offset2) -> Res<()> {
    let off = if o.is_rev() { o.curr() } else { o.next() } ;
    try!(
      self.declare_svars(off).map_err(
        |err| format!(
          "[Unroller::unroll] \
          while declaring state at {}\n{}", off, err
        )
      )
    ) ;
    self.solver.assert(self.sys.trans_term(), o).map_err(
      |err| format!(
        "[Unroller::unroll] \
        while asserting trans at {}\n{}", o, err
      )
    )
  }

  /// Unrolls the transition relation once. **Declares** state variables in
  /// the next offset if the offset is not reversed, in the current offset
  /// otherwise (for backward unrolling).
  ///
  /// Asserts all invariants in the next state.
  pub fn unroll(& mut self, o: & Offset2) -> Res<()> {
    try!( self.just_unroll(o) ) ;
    for inv in self.invs.iter() {
      try!(
        self.solver.assert(inv.next(), o).map_err(
          |err| format!(
            "[Unroller::unroll] \
            while asserting inv {} at {}\n{}", inv, o, err
          )
        )
      ) ;
    }
    Ok(())
  }

  /// Unrolls the transition relation once. **Declares** state variables in
  /// the next offset if the offset is not reversed, in the current offset
  /// otherwise (for backward unrolling).
  ///
  /// Asserts all invariants in the next state, and one-state invariants in
  /// the current state.
  ///
  /// Used
  ///
  /// - in **BMC** at init, to assert one-state invariants at `0` and all
  ///   invariants at `1`.
  /// - in **Kind** for the first (backward) unrolling, to assert all
  ///   invariants at `0` (the last state of the trace) and one-state
  ///   invariants at `1` (the second to last state of the trace).
  pub fn unroll_init(& mut self, o: & Offset2) -> Res<()> {
    try!( self.just_unroll(o) ) ;
    for inv in self.invs.iter() {
      let inv = match * inv {
        STerm::One(ref curr, ref next) => {
          try!(
            self.solver.assert(curr, o).map_err(
              |err| format!(
                "[Unroller::unroll] \
                while asserting one-state inv {} at {}\n{}", inv, o.curr(), err
              )
            )
          ) ;
          next
        },
        STerm::Two(ref next) => next,
      } ;
      try!(
        self.solver.assert(inv, o).map_err(
          |err| format!(
            "[Unroller::unroll] \
            while asserting inv {} at {}\n{}", inv, o, err
          )
        )
      )
    }
    Ok(())
  }

  /// Unrolls the transition relation once. **Declares** state variables in
  /// the next offset if the offset is not reversed, in the current offset
  /// otherwise (for backward unrolling).
  ///
  /// Asserts two-state invariants in the next state, and one-state invariants
  /// in the current state.
  ///
  /// Typically used by **Kind** for backward unrolling, to assert one-state
  /// invariants in the first state of the trace (greater offset) and two-state
  /// invariants in the second state of the trace.
  pub fn unroll_bak(& mut self, o: & Offset2) -> Res<()> {
    try!( self.just_unroll(o) ) ;
    for inv in self.invs.iter() {
      let inv = match * inv {
        STerm::One(ref curr, _) => curr,
        STerm::Two(ref next) => next,
      } ;
      try!(
        self.solver.assert(inv, o).map_err(
          |err| format!(
            "[Unroller::unroll] \
            while asserting inv {} at {}\n{}", inv, o, err
          )
        )
      )
    }
    Ok(())
  }

  /// Memorizes some invariants. **Does not assert anything.**
  #[inline]
  pub fn just_add_invs<
    Collec: IntoIterator< Item = STerm >
  >(& mut self, invs: Collec) {
    use std::iter::Extend ;
    self.invs.extend(invs)
  }

  /// Memorizes some invariants, asserts them between some ranges.
  /// Does nothing if `begin > end`.
  ///
  /// It is a logical error if `begin.is_rev() != end.is_rev()`. Causes panic
  /// in `debug`.
  ///
  /// **If the offsets are not reversed**, asserts one state invariants at
  /// `begin.curr()`, and all invariants for all offsets between `begin` and
  /// `end`. **Inclusive**.
  ///
  /// **If the offsets are reversed**, asserts one state invariants at
  /// `end.curr()`, and all invariants for all offsets between `begin` and
  /// `end`. **Inclusive**.
  pub fn add_invs(
    & mut self, invs: STermSet, begin: & Offset2, end: & Offset2
  ) -> Res<()> {
    debug_assert!( begin.is_rev() == end.is_rev() ) ;
    if begin > end { return Ok(()) }
    let is_rev = begin.is_rev() ;
    let init_off = if ! is_rev { begin } else { end } ;
    for inv in invs.iter() {
      let next = match * inv {
        STerm::One(ref curr, ref next) => {
          try!(
            self.solver.assert(curr, init_off).map_err(
              |err| format!(
                "[Unroller::add_invs] \
                while asserting one-state inv {} at {}\n{}",
                curr, init_off, err
              )
            )
          ) ;
          next
        },
        STerm::Two(ref next) => next,
      } ;
      let mut low = begin.clone() ;
      while end >= & low {
        try!(
          self.solver.assert(next, & low).map_err(
            |err| format!(
              "[Unroller::add_invs] \
              while asserting inv {} at {}\n{}",
              next, low, err
            )
          )
        ) ;
        low = low.nxt()
      }
    }
    self.just_add_invs(invs) ;
    Ok(())
  }

  /// The variables to ask the value of for `get_model`.
  pub fn get_model_vars(& self) -> Vec<Term> {
    use term::{ VarMaker, State } ;
    use sys::real_sys::Callable::* ;

    let mut to_get = Vec::with_capacity( self.sys.state().len() ) ;

    // Retrieve global UFs.
    for fun in self.sys.calls().get() {
      match * * fun {
        Dec(ref fun) => to_get.push(
          self.solver.parser().var( fun.sym().clone() )
        ),
        Def(_) => (),
      }
    }

    // Push state.
    for & (ref sym, _) in self.sys.state().args().iter() {
      to_get.push(
        self.solver.parser().svar( sym.clone(), State::Curr )
      ) ;
      to_get.push(
        self.solver.parser().svar( sym.clone(), State::Next )
      ) ;
    }

    to_get
  }

  /// A model for a precise state (or pair of states) of a system.
  pub fn get_model(& mut self, off: & Offset2) -> Res<Model> {
    use term::Smt2Offset ;
    let vars = self.get_model_vars() ;
    let values = try_str!(
      self.solver.get_values( & vars, off ),
      "could not get values of (state) vars"
    ) ;
    let mut model = Vec::with_capacity( values.len() ) ;
    for ( (term, off), val ) in values.into_iter() {
      let off = match off {
        Smt2Offset::No => None,
        Smt2Offset::One(off) => Some(off),
        Smt2Offset::Two(lo, hi) => return Err(
          format!(
            "unexpected two state ({},{}) term\n\
            terms should be one- or zero-state", lo, hi
          )
        ),
      } ;
      if let real_term::Term::V(ref var) = * term.get() {
        model.push( ( (var.clone(), off), val) )
      } else {
        return Err(
          format!(
            "unexpected term {}\nall terms should be variables", term
          )
        )
      }
    }
    Ok(model)
  }
}


/// Actlit factory.
pub struct ActlitFactory {
  /// Counter for unique actlits.
  count: usize,
}
impl ActlitFactory {
  /// Creates a new actlit factory.
  #[inline]
  pub fn mk() -> Self {
    ActlitFactory { count: 0 }
  }
  /// Creates a new actlit.
  #[inline]
  pub fn mk_fresh(& mut self) -> Actlit {
    let actlit = Actlit {
      count: self.count, offset: Offset2::init()
    } ;
    self.count += 1 ;
    actlit
  }
}

/// Handles fresh activation literal creation, declaration, decativation.
///
/// Also, provides a few helper functions.
pub struct Actlit {
  /// Counter for unique activation literals.
  count: usize,
  /// A dummy offset used to print in the solver.
  offset: Offset2,
}

impl Actlit {

  /// Identifier corresponding to an actlit.
  #[inline]
  pub fn name(& self) -> String {
    format!("| fresh_actlit {}|", self.count)
  }

  /// `TmpTerm` version of an actlit.
  pub fn as_tmp_term(& self) -> TmpTerm {
    TmpTerm::Sym( self.name(), Type::Bool )
  }

  /// Declares an actlit.
  pub fn declare<
    'a, S: SolverTrait<'a>
  >(& self, solver: & mut S) -> SmtRes<()> {
    let (id, ty) = ( self.name(), Type::Bool ) ;
    solver.declare_fun(& id, & [], & ty, & ())
  }

  /// Builds an implication between the actlit and `rhs`.
  pub fn activate_term(& self, rhs: TmpTerm) -> TmpTerm {
    rhs.under_actlit( self.name() )
  }

  /// Deactivates an activation literal.
  pub fn deactivate<
    'a, S: SolverTrait<'a>
  >(self, solver: & mut S) -> UnitSmtRes {
    solver.assert(
      & self.as_tmp_term().tmp_neg(), & self.offset
    )
  }
}

/// Actlit name of a symbol.
fn actlit_name_of_sym(sym: & Sym) -> String {
  format!( "| actlit( {} )|", sym.sym() )
}

/// Actlit name of a property.
fn actlit_name_of(prop: & Prop) -> String {
  actlit_name_of_sym(prop.sym())
}

/// Handles properties by providing a positive actlits for each.
///
/// Also, provides a few helper functions to temporarily inhibit properties.
/// See `inhibit`, `all_inhibited`, `reset_inhibited` and `not_inhibited`.
pub struct TermManager<Key: Hash> {
  /// Map from property name to one-state properties.
  terms_1: HashMap<Key, (Term, Term, TmpTerm, String)>,
  /// Map from property name to two-state properties.
  terms_2: HashMap<Key, (Term, TmpTerm, String)>,
  /// Temporarily inhibited properties.
  inhibited: HashSet<Key>,
}

impl TermManager<Sym> {
  /// Constructs a property manager. Creates and declares one positive
  /// activation literal per property.
  ///
  /// Assumes everything has already been defined.
  pub fn mk<
    'a, S: SolverTrait<'a>
  >(
    props: Vec<Prop>, solver: & mut S
  ) -> Res<Self> {
    // use sys::real_sys::Callable::* ;

    // let calls = sys.calls() ;

    let mut map_1 = HashMap::new() ;
    let mut map_2 = HashMap::new() ;

    for prop in props {
      let actlit = actlit_name_of(& prop) ;
      try_str!(
        solver.declare_fun(
          & actlit, & [], & Type::Bool, & ()
        ),
        "[PropManager::mk] while declaring actlit {}", actlit
      ) ;
      match prop.body().clone() {
        STerm::One(state, next) => {
          let state_impl = state.clone().under_actlit( actlit.clone() ) ;
          let was_there = map_1.insert(
            prop.sym().clone(), (state, next, state_impl, actlit)
          ) ;
          debug_assert!( was_there.is_none() )
        },
        STerm::Two(next) => {
          let next_impl = next.clone().under_actlit( actlit.clone() ) ;
          let was_there = map_2.insert(
            prop.sym().clone(), (next, next_impl, actlit)
          ) ;
          debug_assert!( was_there.is_none() )
        },
      }
    } ;
    let inhibited = HashSet::with_capacity(map_1.len() + map_2.len()) ;
    Ok(
      TermManager {
        terms_1: map_1, terms_2: map_2, inhibited: inhibited
      }
    )
  }
}


impl TermManager<STerm> {
  /// Constructs an STerm manager. Creates and declares one positive
  /// activation literal per Term.
  ///
  /// Assumes everything has already been defined.
  pub fn mk<
    'a, S: SolverTrait<'a>
  >(
    sterms: STermSet, solver: & mut S
  ) -> Res<Self> {
    // use sys::real_sys::Callable::* ;

    // let calls = sys.calls() ;

    let mut map_1 = HashMap::new() ;
    let mut map_2 = HashMap::new() ;

    for sterm in sterms {
      let actlit = format!("| actlit for candidate {}|", sterm.next().hkey()) ;
      try_str!(
        solver.declare_fun(
          & actlit, & [], & Type::Bool, & ()
        ),
        "[TermManager::mk] while declaring actlit {}", actlit
      ) ;
      match sterm.clone() {
        STerm::One(state, next) => {
          let state_impl = state.clone().under_actlit(actlit.clone()) ;
          let was_there = map_1.insert(
            sterm, (state, next, state_impl, actlit)
          ) ;
          debug_assert!( was_there.is_none() )
        },
        STerm::Two(next) => {
          let next_impl = next.clone().under_actlit(actlit.clone()) ;
          let was_there = map_2.insert(
            sterm, (next, next_impl, actlit)
          ) ;
          debug_assert!( was_there.is_none() )
        },
      }
    } ;
    let inhibited = HashSet::with_capacity(map_1.len() + map_2.len()) ;
    Ok(
      TermManager {
        terms_1: map_1, terms_2: map_2, inhibited: inhibited
      }
    )
  }
}



impl<Key: Hash + Clone + Eq + Display> TermManager<Key> {

  /// Removes some terms from a manager.
  pub fn forget<
    'a, 'b, S: SolverTrait<'a>, Keys: Iterator<Item=& 'b Key>
  >(
    & mut self, solver: & mut S, keys: Keys
  ) -> Res<()>
  where Key: 'a + 'b {
    for key in keys {
      let actlit = match self.terms_1.remove(& key) {
        Some( (_, _, _, actlit) ) => actlit,
        None => match self.terms_2.remove(& key) {
          Some( (_, _, actlit) ) => actlit,
          None => continue,
        },
      } ;
      try_str!(
        solver.assert( & format!("(not {})", actlit), & ()),
        "[TermManager::forget] while deactivating {} ({})", key, actlit
      ) ;
    }
    Ok(())
  }

  /// Total number of properties in a manager.
  pub fn len(& self) -> usize { self.terms_1.len() + self.terms_2.len() }

  /// Returns true iff the manager does not have any property left.
  pub fn none_left(& self) -> bool {
    self.terms_1.is_empty() && self.terms_2.is_empty()
  }

  /// Activates all the one-state properties, including inhibited ones, at a
  /// given offset **using their current version** by overloading their
  /// activation literals.
  /// That is, if the offset is `(0,1)` all one-state properties will be
  /// activated at `0`.
  pub fn activate_state<
    'a, S: SolverTrait<'a>
  >(
    & self, solver: & mut S, at: & Offset2
  ) -> UnitSmtRes {
    for (_, & (_, _, ref act, _)) in self.terms_1.iter() {
      try!( solver.assert(act, at) )
    } ;
    Ok(())
  }

  /// Activates all the two-state properties, including inhibited ones, at a
  /// given offset by overloading their activation literals.
  pub fn activate_next<
    'a, S: SolverTrait<'a>
  >(
    & self, solver: & mut S, at: & Offset2
  ) -> UnitSmtRes {
    for (_, & (_, ref act, _)) in self.terms_2.iter() {
      try!( solver.assert(act, at) )
    } ;
    Ok(())
  }

  /// Returns the term corresponding to one of the one-state, non-inhibited
  /// properties being false **in state**.
  pub fn one_false_state(& self) -> Option<TmpTerm> {
    let mut terms = Vec::with_capacity(self.terms_1.len()) ;
    for (ref key, & (ref state, _, _, _)) in self.terms_1.iter() {
      if ! self.inhibited.contains(key) {
        // If manager is well-founded the unwrap cannot fail.
        terms.push( state.clone() )
      }
    } ;
    if terms.is_empty() { None } else {
      Some( TmpTerm::mk_term_conj(& terms).tmp_neg() )
    }
  }

  /// Returns the term corresponding to one of the non-inhibited properties
  /// being false. Uses the next version of one-state.
  pub fn one_false_next(& self) -> Option<TmpTerm> {
    let mut terms = Vec::with_capacity(
      self.terms_1.len() + self.terms_2.len()
    ) ;
    for (ref key, & (_, ref next, _, _)) in self.terms_1.iter() {
      if ! self.inhibited.contains(key) {
        terms.push( next.clone() )
      }
    } ;
    for (ref key, & (ref next, _, _)) in self.terms_2.iter() {
      if ! self.inhibited.contains(key) {
        terms.push( next.clone() )
      }
    } ;
    if terms.is_empty() { None } else {
      Some( TmpTerm::mk_term_conj(& terms).tmp_neg() )
    }
  }

  /// Returns the actlits activating all the non-inhibited properties.
  pub fn actlits(& self) -> Vec<String> {
    let mut vec = Vec::with_capacity(
      self.terms_1.len() + self.terms_2.len()
    ) ;
    for (ref key, & (_, _, _, ref actlit)) in self.terms_1.iter() {
      if ! self.inhibited.contains(key) {
        vec.push( actlit.clone() )
      }
    } ;
    for (ref key, & (_, _, ref actlit)) in self.terms_2.iter() {
      if ! self.inhibited.contains(key) {
        vec.push( actlit.clone() )
      }
    } ;
    vec.shrink_to_fit() ;
    vec
  }

  /// Returns the list of non-inhibited properties that evaluate to false in
  /// their **state** version for some offset in a solver.
  pub fn get_false_state<
    'a, S: SolverTrait<'a>
  >(
    & self, solver: & mut S, o: & Offset2
  ) -> Res<Vec<Key>> {
    let mut terms = Vec::with_capacity(self.terms_1.len()) ;
    let mut back_map = HashMap::with_capacity(self.terms_1.len()) ;
    for (ref key, & (ref state, _, _, _)) in self.terms_1.iter() {
      if ! self.inhibited.contains(key) {
        terms.push(state.clone()) ;
        match back_map.insert(
          state.clone(), key.clone()
        ) {
          None => (),
          Some(old) => return Err(
            format!(
              "term {}\n\
              already mapped to key {}\n\
              trying to map it to {}",
              state, old, key
            )
          ),
        }
      }
    } ;
    let values = try_str!(
      solver.get_values(& terms, o),
      "[TermManager::get_false_state] while retrieving values"
    ) ;
    let mut keys = Vec::with_capacity(7) ;
    for ((t, _), v) in values {
      match * v.get() {
        real_term::Cst::Bool(true) => (),
        real_term::Cst::Bool(false) => keys.push(
          try_str_opt!(
            back_map.remove(& t),
            "[TermManager::get_false_state] unknown term {}", t
          ).clone()
        ),
        _ => return Err(
          format!(
            "[TermManager::get_false_state] unexpected term value {}", v
          )
        )
      }
    } ;
    Ok(keys)
  }

  /// Returns the list of non-inhibited properties that evaluate to false in
  /// their next version for some offset in a solver.
  pub fn get_false_next<
    'a, S: SolverTrait<'a>
  >(
    & self, solver: & mut S, o: & Offset2
  ) -> Res<Vec<Key>> {
    let mut terms = Vec::with_capacity(
      (self.terms_1.len() * 2) + self.terms_2.len()
    ) ;
    // Maps terms back to the property they correspond to.
    let mut back_map = HashMap::with_capacity(
      self.terms_1.len() + self.terms_2.len()
    ) ;
    for (ref key, & (ref state, ref next, _, _)) in self.terms_1.iter() {
      if ! self.inhibited.contains(key) {
        terms.push(next.clone()) ;
        match back_map.insert(
          next.clone(), key.clone()
        ) {
          None => (),
          Some(old) => return Err(
            format!(
              "[TermManager::get_false_next] term {}\n    \
              already mapped to property {}\n    \
              trying to map it to {}",
              next, old, key
            )
          ),
        } ;
        // We also insert state. If there is no two-state property, one-state
        // ones will be parsed as state.
        match back_map.insert(
          state.clone(), key.clone()
        ) {
          None => (),
          Some(old) => return Err(
            format!(
              "[TermManager::get_false_next]term {}\n    \
              already mapped to key {}\n    \
              trying to map it to {}",
              state, old, key
            )
          ),
        } ;
      }
    } ;
    for (ref key, & (ref next, _, _)) in self.terms_2.iter() {
      if ! self.inhibited.contains(key) {
        terms.push(next.clone()) ;
        match back_map.insert(next.clone(), key.clone()) {
          None => (),
          Some(old) => return Err(
            format!(
              "[TermManager::get_false_next]term {}\n    \
              already mapped to key {}\n    \
              trying to map it to {}",
              next, old, key
            )
          ),
        }
      }
    } ;
    let vec = try_str!(
      solver.get_values(& terms, o),
      "while retrieving values of terms at {}", o
    ) ;
    let mut keys = Vec::with_capacity(7) ;
    for ((t, _), v) in vec {
      match * v.get() {
        real_term::Cst::Bool(true) => (),
        real_term::Cst::Bool(false) => match back_map.remove(& t) {
          Some(key) => keys.push( key.clone() ),
          None => {
            let mut s = format!(
              "[TermManager::get_false_next] unknown {}", t
            ) ;
            for (ref t, ref sym) in back_map.iter() {
              s = format!("{}\n  {} -> {}", s, t, sym) ;
            } ;
            return Err(s)
          },
        },
        _ => return Err(
          format!("[TermManager::get_false_next] unexpected prop value {}", v)
        ),
      }
    } ;
    Ok(keys)
  }

  /// Inhibits some properties, meaning `one_false`, `actlits` and `get_false`
  /// will ignore them.
  pub fn inhibit(& mut self, keys: & Vec<Key>) -> Res<()> {
    for key in keys.iter() {
      let was_not_there = self.inhibited.insert(key.clone()) ;
      if ! was_not_there {
        return Err(
          format!(
            "[PropManager::inhibit] inhibited on property already inhibited"
          )
        )
      }
    }
    Ok(())
  }

  /// Returns true iff all properties are inhibited.
  pub fn all_inhibited(& self) -> bool {
    self.inhibited.len() == self.terms_1.len() + self.terms_2.len()
  }

  /// De-inhibits inhibited terms.
  pub fn reset_inhibited(& mut self) {
    self.inhibited.clear()
  }

  /// Returns the terms that are not inhibited.
  pub fn not_inhibited_set(& self) -> HashSet<Key> {
    let mut set = HashSet::with_capacity(
      self.terms_1.len() + self.terms_2.len() - self.inhibited.len()
    ) ;
    for (ref key, _) in self.terms_1.iter() {
      if ! self.inhibited.contains(key) {
        let _ = set.insert((* key).clone()) ;
        ()
      }
    } ;
    for (ref key, _) in self.terms_2.iter() {
      if ! self.inhibited.contains(key) {
        let _ = set.insert((* key).clone()) ;
        ()
      }
    } ;
    debug_assert_eq!(
      set.len(),
      self.terms_1.len() + self.terms_2.len() - self.inhibited.len()
    ) ;
    set.shrink_to_fit() ;
    set
  }

  /// Returns the properties that are not inhibited.
  pub fn not_inhibited(& self) -> Vec<Key> {
    self.not_inhibited_set().into_iter().collect()
  }
}