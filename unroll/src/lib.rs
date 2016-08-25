#![deny(missing_docs)]
// Copyright 2015 Adrien Champion. See the COPYRIGHT file at the top-level
// directory of this distribution.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

/*! Convenience traits and structures for unrolling a system and handling
properties. */

extern crate term ;
extern crate system as sys ;

use std::collections::{ HashSet, HashMap } ;

use term::{
  Factory, Type, Sym, Term, Offset, Offset2, STerm, real_term
} ;
use term::smt::* ;
use term::tmp::* ;

use sys::{ Prop, Sys } ;

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

/** Defines the init and trans predicates of a system. */
fn define<'a, S: Solver<'a, Factory>>(
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



/** Provides helper functions for the unrolling of a transition system. */
pub trait Unroller {
  /** Declares/defines UFs, functions, and system init/trans predicates. */
  fn defclare_funs<
    'a, S: Solver<'a, Factory>
  >(& self, & mut S) -> UnitSmtRes ;
  /** Declares state variables at some offset. */
  #[inline(always)]
  fn declare_svars<
    'a, S: Solver<'a, Factory>
  >(& self, & mut S, & Offset) -> UnitSmtRes ;
  /** Asserts the init predicate. **Declares** state variables in the current
  offset. */
  #[inline(always)]
  fn assert_init<
    'a, S: Solver<'a, Factory>
  >(& self, solver: & mut S, o: & Offset2) -> UnitSmtRes ;
  /** Unrolls the transition relation once. **Declares** state variables in
  the next offset if the offset is not reversed, in the current offset
  otherwise (for backward unrolling). */
  #[inline(always)]
  fn unroll<
    'a, S: Solver<'a, Factory>
  >(& self, solver: & mut S, o: & Offset2) -> UnitSmtRes ;
}
impl Unroller for sys::Sys {
  fn defclare_funs<
    'a, S: Solver<'a, Factory>
  >(& self, solver: & mut S) -> UnitSmtRes {
    use sys::real_sys::Callable::* ;
    // Will not really be used.
    let offset = Offset2::init() ;

    // Declaring UFs and defining functions.
    // println!("declaring UFs, defining funs") ;
    for fun in self.calls().get() {
      // println!("defining {}", fun.sym()) ;
      match * * fun {
        Dec(ref fun) => try!(
          solver.declare_fun( fun.sym(), fun.sig(), fun.typ(), & offset )
        ),
        Def(ref fun) => try!(
          solver.define_fun(
            fun.sym(), fun.args(), fun.typ(), fun.body(), & offset
          )
        ),
      }
    } ;

    // Defining sub systems.
    // println!("defining sub systems") ;
    for & (ref sub, _) in self.subsys() {
      try!( define(sub, solver, & offset) )
    } ;

    // Define current system.
    // println!("defining top system") ;
    define(self, solver, & offset)
  }

  fn declare_svars<
    'a, S: Solver<'a, Factory>
  >(& self, solver: & mut S, o: & Offset) -> UnitSmtRes {
    for & (ref var, ref typ) in self.init().1.iter() {
      try!(
        solver.declare_fun(var, & vec![], typ, o)
      )
    } ;
    Ok(())
  }

  fn assert_init<
    'a, S: Solver<'a, Factory>
  >(& self, solver: & mut S, o: & Offset2) -> UnitSmtRes {
    try!(
      self.declare_svars(solver, o.curr())
    ) ;
    solver.assert(self.init_term(), o)
  }
  fn unroll<
    'a, S: Solver<'a, Factory>
  >(& self, solver: & mut S, o: & Offset2) -> UnitSmtRes {
    let off = if o.is_rev() { o.curr() } else { o.next() } ;
    try!(
      self.declare_svars(solver, off)
    ) ;
    solver.assert(self.trans_term(), o)
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

/** Handles fresh activation literal creation, declaration, decativation.

Also, provides a few helper functions. */
pub struct Actlit {
  /** Counter for unique activation literals. */
  count: usize,
  /** A dummy offset used to print in the solver. */
  offset: Offset2,
}

impl Actlit {
  /** Constructs an actlit generator. */
  #[inline]
  pub fn mk() -> Self {
    Actlit { count: 0, offset: Offset2::init() }
  }

  /** Identifier corresponding to an actlit. */
  #[inline]
  pub fn name(& self) -> String {
    format!("fresh_actlit_{}", self.count)
  }

  /** `TmpTerm` version of an actlit. */
  pub fn as_tmp_term(& self) -> TmpTerm {
    TmpTerm::Sym( self.name(), Type::Bool )
  }

  /** Creates a fresh actlit and declares it. */
  pub fn declare<
    'a, S: Solver<'a, Factory>
  >(& self, solver: & mut S) -> SmtRes<()> {
    let (id, ty) = ( self.name(), Type::Bool ) ;
    solver.declare_fun(& id, & [], & ty, & ())
  }

  /** Builds an implication between the actlit and `rhs`. */
  pub fn activate_term(& self, rhs: TmpTerm) -> TmpTerm {
    rhs.under_actlit( self.name() )
  }

  /** Deactivates an activation literal. */
  pub fn deactivate<
    'a, S: Solver<'a, Factory>
  >(self, solver: & mut S) -> UnitSmtRes {
    solver.assert(
      & self.as_tmp_term(), & self.offset
    )
  }
}

/** Actlit name of a symbol. */
fn actlit_name_of_sym(sym: & Sym) -> String {
  format!( "|actlit( {} )|", sym.sym() )
}

/** Actlit name of a property. */
fn actlit_name_of(prop: & Prop) -> String {
  actlit_name_of_sym(prop.sym())
}

/** Handles properties by providing a positive actlits for each.

Also, provides a few helper functions to temporarily inhibit properties. See
`inhibite`, `all_inhibited`, `reset_inhibited` and `not_inhibited`. */
pub struct PropManager {
  /** Map from property name to one-state properties. */
  props_1: HashMap<Sym, (Prop, TmpTerm)>,
  /** Map from property name to two-state properties. */
  props_2: HashMap<Sym, (Prop, TmpTerm)>,
  /** Dummy offset to print in the solver. */
  offset: Offset2,
  /** Temporarily inhibited properties. */
  inhibited: HashSet<Sym>,
}

impl PropManager {
  /** Constructs a property manager. Creates and declares one positive
  activation literal per property. */
  pub fn mk<
    'a, S: Solver<'a, Factory>
  >(
    props: Vec<Prop>, solver: & mut S, sys: & Sys
  ) -> SmtRes<Self> {
    use sys::real_sys::Callable::* ;

    let calls = sys.calls() ;

    let mut map_1 = HashMap::new() ;
    let mut map_2 = HashMap::new() ;
    let offset = Offset2::init() ;

    for prop in props {
      for call in prop.calls().get() {
        if ! calls.contains(call) {
          match * * call {
            Dec(ref fun) => try!(
              solver.declare_fun(fun.sym(), fun.sig(), fun.typ(), & offset)
            ),
            Def(ref fun) => try!(
              solver.define_fun(
                fun.sym(), fun.args(), fun.typ(), fun.body(), & offset
              )
            ),
          }
        }
      } ;
      let actlit = actlit_name_of(& prop) ;
      match solver.declare_fun(
        & actlit, & [], & Type::Bool, & ()
      ) {
        Ok(()) => (),
        Err(e) => return Err(e),
      }
      match prop.body().clone() {
        STerm::One(ref state, _) => {
          let state_impl = state.under_actlit(actlit) ;
          let was_there = map_1.insert(
            prop.sym().clone(), (prop, state_impl)
          ) ;
          assert!( was_there.is_none() )
        },
        STerm::Two(ref next) => {
          let next_impl = next.under_actlit(actlit) ;
          let was_there = map_2.insert(
            prop.sym().clone(), (prop, next_impl)
          ) ;
          assert!( was_there.is_none() )
        },
      }
    } ;
    let inhibited = HashSet::with_capacity(map_1.len() + map_2.len()) ;
    Ok(
      PropManager {
        props_1: map_1, props_2: map_2,
        offset: offset, inhibited: inhibited
      }
    )
  }

  /** Total number of properties in a manager. */
  pub fn len(& self) -> usize { self.props_1.len() + self.props_2.len() }

  /** Returns true iff the manager does not have any property left. */
  pub fn none_left(& self) -> bool {
    self.props_1.is_empty() && self.props_2.is_empty()
  }

  /** Removes some properties from a manager. */
  pub fn forget<
    'a, S: Solver<'a, Factory>
  >(
    & mut self, solver: & mut S, props: & [Sym]
  ) -> UnitSmtRes {
    for prop in props {
      match self.props_1.remove(& prop) {
        Some(_) => (),
        None => match self.props_2.remove(& prop) {
          Some(_) => (),
          None => continue,
        },
      }

      let deactlit = TmpTerm::Sym(
        actlit_name_of_sym(prop), Type::Bool
      ).tmp_neg() ;
      try!(
        solver.assert( & deactlit, & self.offset )
      )
    } ;
    Ok(())
  }

  /** Activates all the one-state properties, including inhibited ones, at a
  given offset **using their state version** by overloading their activation
  literals.
  That is, if the offset is `(0,1)` all one-state properties will be activated
  at `1`. */
  pub fn activate_state<
    'a, S: Solver<'a, Factory>
  >(
    & self, solver: & mut S, at: & Offset2
  ) -> UnitSmtRes {
    for (_, & (_, ref act)) in self.props_1.iter() {
      try!( solver.assert(act, at) )
    } ;
    Ok(())
  }

  /** Activates all the two-state properties, including inhibited ones, at a
  given offset by overloading their activation literals. */
  pub fn activate_next<
    'a, S: Solver<'a, Factory>
  >(
    & self, solver: & mut S, at: & Offset2
  ) -> UnitSmtRes {
    for (_, & (_, ref act)) in self.props_2.iter() {
      try!( solver.assert(act, at) )
    } ;
    Ok(())
  }

  /** Returns the term corresponding to one of the one state, non-inhibited
  properties being false **in state**. */
  pub fn one_false_state(& self) -> Option<TmpTerm> {
    let mut props = Vec::with_capacity(self.props_1.len()) ;
    for (ref sym, & (ref prop, _)) in self.props_1.iter() {
      if ! self.inhibited.contains(sym) {
        // If manager is well-founded the unwrap cannot fail.
        props.push( prop.body().state().unwrap().clone() )
      }
    } ;
    if props.is_empty() { None } else {
      Some( TmpTerm::mk_term_conj(& props).tmp_neg() )
    }
  }

  /** Returns the term corresponding to one of the non-inhibited properties
  being false. Uses the next version of one-state. */
  pub fn one_false_next(& self) -> Option<TmpTerm> {
    let mut props = Vec::with_capacity(
      self.props_1.len() + self.props_2.len()
    ) ;
    for (ref sym, & (ref prop, _)) in self.props_1.iter() {
      if ! self.inhibited.contains(sym) {
        props.push( prop.body().next().clone() )
      }
    } ;
    for (ref sym, & (ref prop, _)) in self.props_2.iter() {
      if ! self.inhibited.contains(sym) {
        props.push( prop.body().next().clone() )
      }
    } ;
    if props.is_empty() { None } else {
      Some( TmpTerm::mk_term_conj(& props).tmp_neg() )
    }
  }

  /** Returns the actlits activating all the non-inhibited properties. */
  pub fn actlits(& self) -> Vec<String> {
    let mut vec = Vec::with_capacity(
      self.props_1.len() + self.props_2.len()
    ) ;
    for (ref sym, & (ref prop, _)) in self.props_1.iter() {
      if ! self.inhibited.contains(sym) {
        vec.push( actlit_name_of(prop) )
      }
    } ;
    for (ref sym, & (ref prop, _)) in self.props_2.iter() {
      if ! self.inhibited.contains(sym) {
        vec.push( actlit_name_of(prop) )
      }
    } ;
    vec.shrink_to_fit() ;
    vec
  }

  /** Returns the list of non-inhibited one-state properties that evaluate to
  false in their state version for some offset in a solver. */
  pub fn get_false_state<
    'a, S: Solver<'a, Factory> + QueryExprInfo<'a, Factory, Term>
  >(
    & self, solver: & mut S, o: & Offset2
  ) -> SmtRes<Vec<Sym>> {
    let mut terms = Vec::with_capacity(self.props_1.len()) ;
    let mut back_map = HashMap::with_capacity(self.props_1.len()) ;
    for (ref sym, & (ref prop, _)) in self.props_1.iter() {
      if ! self.inhibited.contains(sym) {
        terms.push(prop.body().state().unwrap().clone()) ;
        match back_map.insert(
          prop.body().state().unwrap().clone(), prop.sym().clone()
        ) {
          None => (),
          Some(_) => unreachable!(),
        }
      }
    } ;
    match solver.get_values(& terms, o) {
      Ok(vec) => {
        let mut syms = Vec::with_capacity(7) ;
        for ((t, _), v) in vec {
          match * v.get() {
            real_term::Cst::Bool(true) => (),
            real_term::Cst::Bool(false) => match back_map.remove(& t) {
              Some(sym) => syms.push(sym),
              None => panic!("unknown term {}", t),
            },
            _ => panic!("[unroller.get_values] unexpected prop value {}", v)
          }
        } ;
        Ok(syms)
      },
      Err(e) => Err(e),
    }
  }

  /** Returns the list of non-inhibited properties that evaluate to false in
  their next version for some offset in a solver. */
  pub fn get_false_next<
    'a, S: Solver<'a, Factory> + QueryExprInfo<'a, Factory, Term>
  >(
    & self, solver: & mut S, o: & Offset2
  ) -> SmtRes<Vec<Sym>> {
    let mut terms = Vec::with_capacity(
      (self.props_1.len() * 2) + self.props_2.len()
    ) ;
    let mut back_map = HashMap::with_capacity(
      self.props_1.len() + self.props_2.len()
    ) ;
    for (ref sym, & (ref prop, _)) in self.props_1.iter() {
      if ! self.inhibited.contains(sym) {
        terms.push(prop.body().next().clone()) ;
        match back_map.insert(
          prop.body().next().clone(), prop.sym().clone()
        ) {
          None => (),
          Some(_) => unreachable!(),
        } ;
        // We also insert state. If there is no two-state property, one-state
        // ones will be parsed as state.
        match back_map.insert(
          prop.body().state().unwrap().clone(), prop.sym().clone()
        ) {
          None => (),
          Some(_) => unreachable!(),
        } ;
      }
    } ;
    for (ref sym, & (ref prop, _)) in self.props_2.iter() {
      if ! self.inhibited.contains(sym) {
        terms.push(prop.body().next().clone()) ;
        match back_map.insert(prop.body().next().clone(), prop.sym().clone()) {
          None => (),
          Some(_) => unreachable!(),
        }
      }
    } ;
    match solver.get_values(& terms, o) {
      Ok(vec) => {
        let mut syms = Vec::with_capacity(7) ;
        for ((t, _), v) in vec {
          match * v.get() {
            real_term::Cst::Bool(true) => (),
            real_term::Cst::Bool(false) => match back_map.remove(& t) {
              Some(sym) => syms.push(sym),
              None => {
                let mut s = format!("unknown {}", t) ;
                for (ref t, ref sym) in back_map.iter() {
                  s = format!("{}\n  {} -> {}", s, t, sym) ;
                } ;
                panic!("{}", s)
              },
            },
            _ => panic!("[unroller.get_values] unexpected prop value {}", v)
          }
        } ;
        Ok(syms)
      },
      Err(e) => Err(e),
    }
  }

  /** Inhibits some properties, meaning `one_false`, `actlits` and `get_false`
  will ignore them. */
  pub fn inhibit(& mut self, props: & Vec<Sym>) {
    for prop in props.iter() {
      let was_not_there = self.inhibited.insert(prop.clone()) ;
      if ! was_not_there {
        panic!("[manager.inhibited] inhibited on property already inhibited")
      }
    }
  }

  /** Returns true iff all properties are inhibited. */
  pub fn all_inhibited(& self) -> bool {
    self.inhibited.len() == self.props_1.len() + self.props_2.len()
  }

  /** De-inhibits inhibited properties. */
  pub fn reset_inhibited(& mut self) {
    self.inhibited.clear()
  }

  /** Returns the properties that are not inhibited. */
  pub fn not_inhibited(& self) -> Vec<Sym> {
    let mut vec = Vec::with_capacity(
      self.props_1.len() + self.props_2.len() - self.inhibited.len()
    ) ;
    for (ref sym, _) in self.props_1.iter() {
      if ! self.inhibited.contains(sym) { vec.push((* sym).clone()) }
    } ;
    for (ref sym, _) in self.props_2.iter() {
      if ! self.inhibited.contains(sym) { vec.push((* sym).clone()) }
    } ;
    vec
  }
}