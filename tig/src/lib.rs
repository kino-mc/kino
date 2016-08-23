// Copyright 2015 Adrien Champion. See the COPYRIGHT file at the top-level
// directory of this distribution.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

#![deny(missing_docs)]
#![allow(dead_code)]

//! Tinelli-style invariant generation.

extern crate term ;
extern crate system ;
#[ macro_use(try_str, try_strs) ]
extern crate common ;
extern crate unroll ;

use std::fmt::Display ;

use term::{
  Factory, Term, Cst,
  Bool, Int, Rat,
} ;

/** Cached evaluator. */
pub mod eval ;
/** Chain (result of splitting an equivalence class. */
pub mod chain ;
/** Graph representing the knowledge learnt by the invariant generation
technique. */
pub mod graph ;




/** Trait for domains.

Domains define the type of the values the candidate terms evaluate to and a
total order relation used for the edges in the graph. */
pub trait Domain : PartialEq + Eq + PartialOrd + Ord + Clone + Display {
  /** A value from a constant. */
  fn of_cst(& Cst) -> Result<Self, String> ;
  /** Creates a term encoding a relation between terms. */
  fn mk_cmp(& mut Factory, Term, Term) -> Term ;
}
impl Domain for Bool {
  fn of_cst(cst: & Cst) -> Result<Self, String> {
    match * cst.get() {
      ::term::real_term::Cst::Bool(b) => Ok(b),
      ref cst => Err(
        format!("[Bool::of_cst] unexpected constant {}", cst)
      ),
    }
  }
  fn mk_cmp(f: & mut Factory, lhs: Term, rhs: Term) -> Term {
    f.imp(lhs, rhs)
  }
}
impl Domain for Int  {
  fn of_cst(cst: & Cst) -> Result<Self, String> {
    match * cst.get() {
      ::term::real_term::Cst::Int(ref i) => Ok(i.clone()),
      ref cst => Err(
        format!("[Int::of_cst] unexpected constant {}", cst)
      ),
    }
  }
  fn mk_cmp(f: & mut Factory, lhs: Term, rhs: Term) -> Term {
    f.le(lhs, rhs)
  }
}
impl Domain for Rat  {
  fn of_cst(cst: & Cst) -> Result<Self, String> {
    match * cst.get() {
      ::term::real_term::Cst::Rat(ref r) => Ok(r.clone()),
      ref cst => Err(
        format!("[Rat::of_cst] unexpected constant {}", cst)
      ),
    }
  }
  fn mk_cmp(f: & mut Factory, lhs: Term, rhs: Term) -> Term {
    f.le(lhs, rhs)
  }
}
