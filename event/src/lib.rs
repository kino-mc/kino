#![deny(missing_docs)]
// Copyright 2015 Adrien Champion. See the COPYRIGHT file at the top-level
// directory of this distribution.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

/*! Messages, structures for receiving and sending messages.

# To do

* check that first argument of custom technique is legal

*/

extern crate ansi_term as ansi ;
extern crate term ;
extern crate system as sys ;

use std::fmt ;

use sys::{ Prop, Sys } ;

pub mod msg ;
pub mod log ;

/** Trait the techniques should implement so that kino can call them in a
generic way. */
pub trait CanRun {
  /** The identifier of the technique. */
  fn id(& self) -> Technique ;
  /** Runs the technique. */
  fn run(& self, sys: Sys, props: Vec<Prop>, event: msg::Event) ;
}

/** Enumeration of the techniques. */
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Technique {
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
impl fmt::Display for Technique {
  fn fmt(& self, fmt: & mut fmt::Formatter) -> fmt::Result {
    write!(fmt, "{}", self.to_str())
  }
}
impl Technique {
  /** A short string representation of a technique. */
  #[inline(always)]
  pub fn to_str(& self) -> & str {
    use Technique::* ;
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
    use Technique::* ;
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
    use Technique::* ;
    match * self {
      Kino => panic!("thread name of supervisor requested"),
      Bmc => "kino_bmc".to_string(),
      KInd => "kino_k-induction".to_string(),
      Tec(ref s, _) => format!("kino_{}", s),
    }
  }
}



// pub struct EventBuilder {
//   r: Sender<MsgUp>,
// }
// impl EventBuilder {
//   pub fn mk(r: Sender<MsgUp>) -> Self { EventBuilder { r: r } }
//   pub fn event(self, t: Technique) -> Event { Event::mk(self.r, t) }
// }

