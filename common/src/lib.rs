#![deny(missing_docs)]
// Copyright 2015 Adrien Champion. See the COPYRIGHT file at the top-level
// directory of this distribution.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

/*! Stuff common to all techniques.

# To do

* check that first argument of custom technique is legal

*/

extern crate ansi_term as ansi ;
#[macro_use]
extern crate nom ;
extern crate term ;
extern crate system as sys ;

use std::fmt ;
use std::sync::Arc ;

use sys::{ Prop, Sys } ;

pub mod msg ;
pub mod log ;
pub mod conf ;


/** Try for `Result<T, String>` to `Result<T, Vec<String>>` that appends
something to error messages. */
#[macro_export]
macro_rules! try_str {
  ($e:expr, $($blah:expr),+) => (
    match $e {
      Ok(res) => res,
      Err(msg) => return Err(
        vec![
          format!( $($blah),+ ), msg
        ]
      ),
    }
  ) ;
}


/** Try for `Result<T, Vec<String>>` to `Result<T, Vec<String>>` that appends
something to error messages. */
#[macro_export]
macro_rules! try_strs {
  ($e:expr, $($blah:expr),+) => (
    match $e {
      Ok(res) => res,
      Err(mut msg) => {
        msg.push( format!( $($blah),+ ) ) ;
        return Err(msg)
      },
    }
  ) ;
}

/** Result yielding a list of strings. */
pub type Res<T> = Result<T, Vec<String>> ;

/** Trait the techniques should implement so that kino can call them in a
generic way. */
pub trait CanRun<Conf> {
  /** The identifier of the technique. */
  fn id(& self) -> Tek ;
  /** Runs the technique. */
  fn run(& self, Arc<Conf>, Sys, Vec<Prop>, msg::Event) ;
}

/** Enumeration of the techniques. */
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Tek {
  /** Master. */
  Kino,
  /** Bounded model checking. */
  Bmc,
  /** Induction. */
  KInd,
  /** Custom technique.
  First string is a short description that should be a legal filename.
  Second is an arbitrarily long description. */
  Tec(& 'static str, & 'static str),
}
impl fmt::Display for Tek {
  fn fmt(& self, fmt: & mut fmt::Formatter) -> fmt::Result {
    write!(fmt, "{}", self.to_str())
  }
}
impl Tek {
  /** A short string representation of a technique. */
  #[inline(always)]
  pub fn to_str(& self) -> & str {
    use Tek::* ;
    match * self {
      Kino => "master",
      Bmc => "bmc",
      KInd => "k-ind",
      Tec(ref s, _) => & s,
    }
  }
  /** A description of a technique. */
  #[inline(always)]
  pub fn desc(& self) -> & str {
    use Tek::* ;
    match * self {
      Kino => "supervisor",
      Bmc => "bounded model checking",
      KInd => "k-induction",
      Tec(_, ref desc) => & desc,
    }
  }
  /** Thread name for techniques. */
  #[inline(always)]
  pub fn thread_name(& self) -> String {
    use Tek::* ;
    match * self {
      Kino => panic!("thread name of supervisor requested"),
      Bmc => "kino_bmc".to_string(),
      KInd => "kino_k-induction".to_string(),
      Tec(ref s, _) => format!("kino_{}", s),
    }
  }
}