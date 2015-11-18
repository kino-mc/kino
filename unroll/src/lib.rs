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

use term::* ;
use term::smt::* ;

use sys::{ Prop } ;

/** Defines the init and trans predicates of a system. */
fn define(
  sys: & sys::Sys, solver: & mut Solver, o: & Offset2
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
  fn defclare_funs(& self, & mut Solver) -> UnitSmtRes ;
  /** Declares state variables at some offset. */
  #[inline(always)]
  fn declare_svars(& self, & mut Solver, & Offset) -> UnitSmtRes ;
  /** Asserts the init predicate. **Declares** state variables in the current
  offset. */
  #[inline(always)]
  fn assert_init(
    & self, solver: & mut Solver, o: & Offset2
  ) -> UnitSmtRes ;
  /** Unrolls the transition relation once. **Declares** state variables in
  the next offset if the offset is not reversed, in the current offset
  otherwise (for backward unrolling). */
  #[inline(always)]
  fn unroll(
    & self, solver: & mut Solver, o: & Offset2
  ) -> UnitSmtRes ;
}
impl Unroller for sys::Sys {
  fn defclare_funs(& self, solver: & mut Solver) -> UnitSmtRes {
    use sys::real_sys::Callable::* ;
    // Will not really be used.
    let offset = Offset2::init() ;

    // Declaring UFs and defining functions.
    for fun in self.calls() {
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
    for & (ref sub, _) in self.subsys() {
      try!( define(sub, solver, & offset) )
    } ;

    // Define current system.
    define(self, solver, & offset)
  }

  fn declare_svars(
    & self, solver: & mut Solver, o: & Offset
  ) -> UnitSmtRes {
    for & (ref var, ref typ) in self.init().1.iter() {
      try!(
        solver.declare_fun(var, & vec![], typ, o)
      )
    } ;
    Ok(())
  }

  fn assert_init(
    & self, solver: & mut Solver, o: & Offset2
  ) -> UnitSmtRes {
    try!(
      self.declare_svars(solver, o.curr())
    ) ;
    solver.assert(self.init_term(), o)
  }
  fn unroll(
    & self, solver: & mut Solver, o: & Offset2
  ) -> UnitSmtRes {
    let off = if o.is_rev() { o.curr() } else { o.next() } ;
    try!(
      self.declare_svars(solver, off)
    ) ;
    solver.assert(self.trans_term(), o)
  }
}

/** Handles fresh activation literal creation, declaration, decativation.

Also, provides a few helper functions. */
pub struct Actlit {
  /** Factory used to create actlits. */
  factory: Factory,
  /** Counter for unique activation literals. */
  count: usize,
  /** A dummy offset used to print in the solver. */
  offset: Offset2,
}

impl Actlit {
  /** Constructs an actlit generator. */
  pub fn mk(factory: Factory) -> Self {
    Actlit { factory: factory, count: 0, offset: Offset2::init() }
  }

  /** Creates a fresh actlit and declares it. */
  pub fn mk_fresh_declare(
    & mut self, solver: & mut Solver
  ) -> SmtRes<::term::Var> {
    use term::{ VarMaker, SymMaker } ;
    let fresh: Var = self.factory.var(
      self.factory.sym(format!("fresh_actlit_{}", self.count))
    ) ;
    self.count = self.count + 1 ;
    match solver.declare_fun(
      & fresh, & [], & Type::Bool, self.offset.curr()
    ) {
      Ok(()) => Ok(fresh),
      Err(e) => Err(e),
    }
  }

  /** Turns an actlit into a term. */
  pub fn to_term(& self, actlit: & Var) -> Term {
    self.factory.mk_var(actlit.clone())
  }

  /** Builds an implication between the actlit and `rhs`. */
  pub fn mk_impl(
    & self, actlit: & Var, rhs: Term
  ) -> Term {
    self.factory.imp( self.factory.mk_var(actlit.clone()), rhs )
  }

  /** Deactivates an activation literal. */
  pub fn deactivate(
    & self, actlit: Var, solver: & mut Solver
  ) -> UnitSmtRes {
    solver.assert(
      & self.factory.not(self.factory.mk_var(actlit)), & self.offset
    )
  }
}

/** Handles properties by providing a positive actlits for each.

Also, provides a few helper functions to temporarily inhibit properties. See
`inhibite`, `all_inhibited`, `reset_inhibited` and `not_inhibited`. */
pub struct PropManager {
  /** Factory to create actlits. */
  factory: Factory,
  /** Map from property name to one-state properties. */
  props_1: HashMap<Sym, (Prop, Var, Term)>,
  /** Map from property name to two-state properties. */
  props_2: HashMap<Sym, (Prop, Var, Term)>,
  /** Dummy offset to print in the solver. */
  offset: Offset2,
  /** Temporarily inhibited properties. */
  inhibited: HashSet<Sym>,
}

impl PropManager {
  /** Constructs a property manager. Creates and declares one positive
  activation literal per property. */
  pub fn mk(
    factory: Factory, props: Vec<Prop>, solver: & mut Solver
  ) -> SmtRes<Self> {
    let mut map_1 = HashMap::new() ;
    let mut map_2 = HashMap::new() ;
    let offset = Offset2::init() ;
    for prop in props {
      let fresh: Var = factory.var(
        factory.sym(format!("activate({})", prop.sym().get().sym()))
      ) ;
      match solver.declare_fun(
        & fresh, & [], & Type::Bool, offset.curr()
      ) {
        Ok(()) => (),
        Err(e) => return Err(e),
      }
      match prop.body().clone() {
        STerm::One(ref state, _) => {
          let state_impl = factory.imp(
            factory.mk_var(fresh.clone()), state.clone()
          ) ;
          let was_there = map_1.insert(
            prop.sym().clone(), (prop, fresh, state_impl)
          ) ;
          assert!(was_there.is_none())
        },
        STerm::Two(ref next) => {
          let next_impl = factory.imp(
            factory.mk_var(fresh.clone()), next.clone()
          ) ;
          let was_there = map_2.insert(
            prop.sym().clone(), (prop, fresh, next_impl)
          ) ;
          assert!(was_there.is_none())
        },
      }
    } ;
    let inhibited = HashSet::with_capacity(map_1.len() + map_2.len()) ;
    Ok(
      PropManager {
        factory: factory,
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
  pub fn forget(
    & mut self, solver: & mut Solver, props: & [Sym]
  ) -> UnitSmtRes {
    for prop in props {
      let actlit = match self.props_1.remove(& prop) {
        Some( (_, actlit, _) ) => actlit,
        None => match self.props_2.remove(& prop) {
          Some ( (_, actlit, _) ) => actlit,
          None => continue
        },
      } ;
      try!(
        solver.assert(
          & self.factory.not( self.factory.mk_var(actlit) ), & self.offset
        )
      )
    } ;
    Ok(())
  }

  /** Activates all the one-state properties, including inhibited ones, at a
  given offset **using their state version** by overloading their activation
  literals.
  That is, if the offset is `(0,1)` all one-state properties will be activated
  at `1`. */
  pub fn activate_state(
    & self, solver: & mut Solver, at: & Offset2
  ) -> UnitSmtRes {
    for (_, & (_, _, ref act)) in self.props_1.iter() {
      try!( solver.assert(act, at) )
    } ;
    Ok(())
  }

  /** Activates all the two-state properties, including inhibited ones, at a
  given offset by overloading their activation literals. */
  pub fn activate_next(
    & self, solver: & mut Solver, at: & Offset2
  ) -> UnitSmtRes {
    for (_, & (_, _, ref act)) in self.props_2.iter() {
      try!( solver.assert(act, at) )
    } ;
    Ok(())
  }

  /** Returns the term corresponding to one of the one state, non-inhibited
  properties being false **in state**. */
  pub fn one_false_state(& self) -> Option<Term> {
    let mut props = Vec::with_capacity(self.props_1.len()) ;
    for (ref sym, & (ref prop, _, _)) in self.props_1.iter() {
      if ! self.inhibited.contains(sym) {
        // If manager is well-founded the unwrap cannot fail.
        props.push( prop.body().state().unwrap().clone() )
      }
    } ;
    if props.is_empty() { None } else {
      Some( self.factory.not( self.factory.and(props) ) )
    }
  }

  /** Returns the term corresponding to one of the non-inhibited properties
  being false. Uses the next version of one-state. */
  pub fn one_false_next(& self) -> Option<Term> {
    let mut props = Vec::with_capacity(
      self.props_1.len() + self.props_2.len()
    ) ;
    for (ref sym, & (ref prop, _, _)) in self.props_1.iter() {
      if ! self.inhibited.contains(sym) {
        props.push( prop.body().next().clone() )
      }
    } ;
    for (ref sym, & (ref prop, _, _)) in self.props_2.iter() {
      if ! self.inhibited.contains(sym) {
        props.push( prop.body().next().clone() )
      }
    } ;
    if props.is_empty() { None } else {
      Some( self.factory.not( self.factory.and(props) ) )
    }
  }

  /** Returns the actlits activating all the non-inhibited properties. */
  pub fn actlits(& self) -> Vec<Var> {
    let mut vec = Vec::with_capacity(
      self.props_1.len() + self.props_2.len()
    ) ;
    for (ref sym, & (_, ref act, _)) in self.props_1.iter() {
      if ! self.inhibited.contains(sym) {
        vec.push(act.clone())
      }
    } ;
    for (ref sym, & (_, ref act, _)) in self.props_2.iter() {
      if ! self.inhibited.contains(sym) {
        vec.push(act.clone())
      }
    } ;
    vec.shrink_to_fit() ;
    vec
  }

  /** Returns the list of non-inhibited one-state properties that evaluate to
  false in their state version for some offset in a solver. */
  pub fn get_false_state(
    & self, solver: & mut Solver, o: & Offset2
  ) -> SmtRes<Vec<Sym>> {
    use term::smt::sync::SyncedExprPrint ;
    let mut terms = Vec::with_capacity(self.props_1.len()) ;
    let mut back_map = HashMap::with_capacity(self.props_1.len()) ;
    for (ref sym, & (ref prop, _, _)) in self.props_1.iter() {
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
  pub fn get_false_next(
    & self, solver: & mut Solver, o: & Offset2
  ) -> SmtRes<Vec<Sym>> {
    use term::smt::sync::SyncedExprPrint ;
    let mut terms = Vec::with_capacity(
      (self.props_1.len() * 2) + self.props_2.len()
    ) ;
    let mut back_map = HashMap::with_capacity(
      self.props_1.len() + self.props_2.len()
    ) ;
    for (ref sym, & (ref prop, _, _)) in self.props_1.iter() {
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
    for (ref sym, & (ref prop, _, _)) in self.props_2.iter() {
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