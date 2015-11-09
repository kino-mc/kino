#![allow(non_upper_case_globals)]
// Copyright 2015 Adrien Champion. See the COPYRIGHT file at the top-level
// directory of this distribution.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

/*! Transition system library.

## Hash consing

[`Sym`][sym type] and [`Term`][term type] come from the kinō
[`term`][term crate] crate and are hash consed. Remember that one should
**never** create more that one [Factory][factory struct] for these. It is
thread-safe and can be cloned.
[`Context`][context struct] holds one for parsing.

## To do

* more clever input consumption in [`Context`][context struct]
* less copy in [`Context`][context struct]

[sym type]: ../term/type.Sym.html (Sym type)
[term type]: ../term/type.Term.html (Term type)
[term crate]: ../term/index.html (term crate)
[factory struct]: ../term/struct.Factory.html (Factory struct)
[context struct]: ctxt/struct.Context.html (Context struct)
*/


#[macro_use]
extern crate nom ;
extern crate rsmt2 ;
extern crate term ;

use std::sync::Arc ;

mod base ;

mod parse ;

/** Real types of the elements of a context. */
pub mod real {
  pub use base::{
    Sig, Args, Uf, Fun, Prop, Sys, Callable
  } ;
}

/** Reads and remembers what has been read. */
pub mod ctxt {
  pub use super::base::Callable ;
  pub use super::parse::{
    Res, Context
  } ;
  pub use super::parse::check::Error ;
}

pub use base::{ CallSet, PropSet } ;

/** A signature, a list of types. Used only in `Uf`. */
pub type Sig = Arc<base::Sig> ;
/** A list of typed formal parameters. */
pub type Args = Arc<base::Args> ;
/** An uninterpreted function. */
pub type Uf = Arc<base::Uf> ;
/** A function (actually a macro in SMT-LIB). */
pub type Fun = Arc<base::Fun> ;
/** Wraps an (uninterpreted) function. */
pub type Callable = Arc<base::Callable> ;
/** A property. */
pub type Prop = Arc<base::Prop> ;
/** A transition system. */
pub type Sys = Arc<base::Sys> ;

pub mod smt {
  pub use rsmt2::{ Solver, UnitSmtRes } ;
  use term::{ Type, Factory, Offset, Offset2, State } ;

  /** Defines the init and trans predicates of a system. */
  fn define(
    sys: & ::Sys, solver: & mut Solver<Factory>, o: & Offset2
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
    fn defclare_funs(& self, & mut Solver<Factory>) -> UnitSmtRes ;
    /** Declares state variables at some offset. */
    fn declare_svars(& self, & mut Solver<Factory>, & Offset) -> UnitSmtRes ;
  }
  impl Unroller for ::Sys {
    fn defclare_funs(& self, solver: & mut Solver<Factory>) -> UnitSmtRes {
      use ::real::Callable::* ;
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
      & self, solver: & mut Solver<Factory>, o: & Offset
    ) -> UnitSmtRes {
      for & (ref var, ref typ) in self.init().1.iter() {
        try!(
          solver.declare_fun(var, & vec![], typ, o)
        )
      } ;
      Ok(())
    }
  }
}