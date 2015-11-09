// Copyright 2015 Adrien Champion. See the COPYRIGHT file at the top-level
// directory of this distribution.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

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




pub trait Unroller {
  /** Declares/defines UFs, functions, and system init/trans predicates. */
  fn defclare_funs(& self, & mut Solver) -> UnitSmtRes ;
  /** Declares state variables at some offset. */
  fn declare_svars(& self, & mut Solver, & Offset) -> UnitSmtRes ;
  /** Asserts the init predicate. **Declares** state variables in the current
  offset. */
  fn assert_init(
    & self, solver: & mut Solver, o: & Offset2
  ) -> UnitSmtRes ;
  /** Unrolls the transition relation once. **Declares** state variables in
  the next offset. */
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
    try!(
      self.declare_svars(solver, o.next())
    ) ;
    solver.assert(self.trans_term(), o)
  }
}

pub struct Actlit {
  factory: Factory,
  count: usize,
  offset: Offset2,
}
impl Actlit {
  pub fn mk(factory: Factory) -> Self {
    Actlit { factory: factory, count: 0, offset: Offset2::init() }
  }
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
  pub fn to_term(& self, actlit: & Var) -> Term {
    self.factory.mk_var(actlit.clone())
  }
  pub fn mk_impl(
    & self, actlit: & Var, rhs: Term
  ) -> Term {
    use term::{ OpMaker, Operator } ;
    self.factory.op(
      Operator::Impl, vec![ self.factory.mk_var(actlit.clone()), rhs ]
    )
  }
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

pub struct PropManager {
  factory: Factory,
  props: HashMap<Sym, (Prop, Var, Term)>,
  offset: Offset2,
  no_check: HashSet<Sym>,
}
impl PropManager {
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
    let no_check = HashSet::with_capacity(map.len()) ;
    Ok(
      PropManager {
        factory: factory, props: map, offset: offset, no_check: no_check
      }
    )
  }
  pub fn len(& self) -> usize { self.props.len() }
  pub fn none_left(& self) -> bool { self.props.is_empty() }
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
  pub fn activate(
    & self, solver: & mut Solver, at: & Offset2
  ) -> UnitSmtRes {
    for (_, & (_, _, ref term)) in self.props.iter() {
      try!( solver.assert(term, at) )
    } ;
    Ok(())
  }
  pub fn one_false(& self) -> Term {
    let mut props = Vec::with_capacity(self.props.len()) ;
    for (ref sym, & (ref prop, _, _)) in self.props.iter() {
      if ! self.no_check.contains(sym) {
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
  pub fn actlits(& self) -> Vec<Var> {
    let mut vec = Vec::with_capacity(self.props.len()) ;
    for (ref sym, & (_, ref act, _)) in self.props.iter() {
      if ! self.no_check.contains(sym) {
        vec.push(act.clone())
      }
    } ;
    vec
  }
  pub fn get_false(
    & self, solver: & mut Solver, o: & Offset2
  ) -> SmtRes<Vec<Sym>> {
    use term::smt::sync::SyncedExprPrint ;
    let mut terms = Vec::with_capacity(self.props.len()) ;
    let mut back_map = HashMap::with_capacity(self.props.len()) ;
    for (ref sym, & (ref prop, _, _)) in self.props.iter() {
      if ! self.no_check.contains(sym) {
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
  pub fn no_check(& mut self, props: & Vec<Sym>) {
    for prop in props.iter() {
      let was_not_there = self.no_check.insert(prop.clone()) ;
      if ! was_not_there {
        panic!("[manager.no_check] no_check on property already not checked")
      }
    }
  }
  pub fn check_is_empty(& self) -> bool {
    self.no_check.len() == self.props.len()
  }
  pub fn reset_no_check(& mut self) {
    self.no_check.clear()
  }
  /** Returns the properties that are not inhibited. */
  pub fn get_checked(& self) -> Vec<Sym> {
    let mut vec = Vec::with_capacity(self.props.len() - self.no_check.len()) ;
    for (ref sym, _) in self.props.iter() {
      if ! self.no_check.contains(sym) { vec.push((* sym).clone()) }
    } ;
    vec
  }
}