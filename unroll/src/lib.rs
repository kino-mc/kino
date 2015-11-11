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
extern crate system ;

use std::collections::{ HashSet, HashMap } ;

use term::* ;
use term::smt::* ;

use system::Prop ;

/** Defines the init and trans predicates of a system. */
fn define(
  sys: & system::Sys, solver: & mut Solver, o: & Offset2
) -> UnitSmtRes {
  let init = sys.init() ;
  // let mut init_args = Vec::with_capacity(init.1.len()) ;
  // for &(ref v, ref typ) in init.1.iter() {
  //   init_args.push( ( (v, o), * typ ) ) ;
  // } ;
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
  // let mut trans_args = Vec::with_capacity(trans.1.len()) ;
  // for &(ref v, ref typ) in trans.1.iter() {
  //   trans_args.push( ( (v, o), * typ ) ) ;
  // } ;
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
impl Unroller for system::Sys {
  fn defclare_funs(& self, solver: & mut Solver) -> UnitSmtRes {
    use system::real::Callable::* ;
    // Will not really be used.
    let offset = Offset2::init() ;

    // Declaring UFs and defining functions.
    for fun in self.calls() {
      match * * fun {
        Dec(ref fun) => {
          try!(
            solver.declare_fun( fun.sym(), fun.sig(), fun.typ(), & offset )
          ) ;
        },
        Def(ref fun) => {
          // let mut args = Vec::with_capacity(fun.args().len()) ;
          // for & (ref sym, ref typ) in fun.args() {
          //   args.push( ( (* sym.get()).clone(), * typ) )
          // } ;
          try!(
            solver.define_fun(
              fun.sym(),
              fun.args(),
              fun.typ(),
              fun.body(),
              & offset
            )
          )
        },
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
    let fresh = self.factory.var_consign().var(
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
    use term::{ OpMaker, Operator } ;
    self.factory.op(
      Operator::Impl, vec![ self.factory.mk_var(actlit.clone()), rhs ]
    )
  }

  /** Deactivates an activation literal. */
  pub fn deactivate(
    & self, actlit: Var, solver: & mut Solver
  ) -> UnitSmtRes {
    use term::{ OpMaker, Operator } ;
    solver.assert(
      & self.factory.op(
        Operator::Not, vec![ self.factory.mk_var(actlit) ]
      ), & self.offset
    )
  }
}

/** Handles properties by providing a positive actlits for each.

Also, provides a few helper functions to temporarily inhibit properties. See
`inhibite`, `all_inhibited`, `reset_inhibited` and `not_inhibited`. */
pub struct PropManager {
  /** Factory to create actlits. */
  factory: Factory,
  /** Map from property name to property. */
  props: HashMap<Sym, (Prop, Var, Term)>,
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
    let mut map = HashMap::new() ;
    let offset = Offset2::init() ;
    for prop in props {
      let fresh = factory.var_consign().var(
        factory.sym(format!("activate({})", prop.sym().get().sym()))
      ) ;
      match solver.declare_fun(
        & fresh, & [], & Type::Bool, offset.curr()
      ) {
        Ok(()) => (),
        Err(e) => return Err(e),
      }
      let term = factory.op(
        Operator::Impl,
        vec![
          factory.mk_var(fresh.clone()),
          prop.body().clone()
        ]
      ) ;
      let was_there = map.insert( prop.sym().clone(), (prop, fresh, term) ) ;
      assert!(was_there.is_none())
    } ;
    let inhibited = HashSet::with_capacity(map.len()) ;
    Ok(
      PropManager {
        factory: factory, props: map, offset: offset, inhibited: inhibited
      }
    )
  }

  /** Total number of properties in a manager. */
  pub fn len(& self) -> usize { self.props.len() }

  /** Returns true iff the manager does not have any property left. */
  pub fn none_left(& self) -> bool { self.props.is_empty() }

  /** Removes some properties from a manager. */
  pub fn forget(
    & mut self, solver: & mut Solver, props: & [Sym]
  ) -> UnitSmtRes {
    for prop in props {
      match self.props.remove(& prop) {
        Some( (_, actlit, _) ) => try!(
          solver.assert(
            & self.factory.op(
              Operator::Not, vec![ self.factory.mk_var(actlit) ]
            ), & self.offset
          )
        ),
        None => (),
      }
    } ;
    Ok(())
  }

  /** Activates all the properties, including inhibited ones, at a given
  offset by overloading their activation literals. */
  pub fn activate(
    & self, solver: & mut Solver, at: & Offset2
  ) -> UnitSmtRes {
    for (_, & (_, _, ref term)) in self.props.iter() {
      try!( solver.assert(term, at) )
    } ;
    Ok(())
  }

  /** Returns the term corresponding to one of the non-inhibited properties
  being false. */
  pub fn one_false(& self) -> Term {
    let mut props = Vec::with_capacity(self.props.len()) ;
    for (ref sym, & (ref prop, _, _)) in self.props.iter() {
      if ! self.inhibited.contains(sym) {
        props.push( prop.body().clone() )
      }
    } ;
    self.factory.op(
      Operator::Not,
      vec![
        self.factory.op(
          Operator::And,
          props
        )
      ]
    )
  }

  /** Returns the actlits activating all the non-inhibited properties. */
  pub fn actlits(& self) -> Vec<Var> {
    let mut vec = Vec::with_capacity(self.props.len()) ;
    for (ref sym, & (_, ref act, _)) in self.props.iter() {
      if ! self.inhibited.contains(sym) {
        vec.push(act.clone())
      }
    } ;
    vec
  }

  /** Returns the list of non-inhibited properties that evaluate to false for
  some offset in a solver. */
  pub fn get_false(
    & self, solver: & mut Solver, o: & Offset2
  ) -> SmtRes<Vec<Sym>> {
    use term::smt::sync::SyncedExprPrint ;
    let mut terms = Vec::with_capacity(self.props.len()) ;
    let mut back_map = HashMap::with_capacity(self.props.len()) ;
    for (ref sym, & (ref prop, _, _)) in self.props.iter() {
      if ! self.inhibited.contains(sym) {
        terms.push(prop.body().clone()) ;
        match back_map.insert(prop.body().clone(), prop.sym().clone()) {
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
            term::real::Cst::Bool(true) => (),
            term::real::Cst::Bool(false) => match back_map.remove(& t) {
              Some(sym) => syms.push(sym),
              None => unreachable!(),
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
        panic!("[manager.inhibited] inhibited on property already not checked")
      }
    }
  }

  /** Returns true iff all properties are inhibited. */
  pub fn all_inhibited(& self) -> bool {
    self.inhibited.len() == self.props.len()
  }

  /** De-inhibits inhibited properties. */
  pub fn reset_inhibited(& mut self) {
    self.inhibited.clear()
  }

  /** Returns the properties that are not inhibited. */
  pub fn not_inhibited(& self) -> Vec<Sym> {
    let mut vec = Vec::with_capacity(self.props.len() - self.inhibited.len()) ;
    for (ref sym, _) in self.props.iter() {
      if ! self.inhibited.contains(sym) { vec.push((* sym).clone()) }
    } ;
    vec
  }
}