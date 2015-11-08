// Copyright 2015 Adrien Champion. See the COPYRIGHT file at the top-level
// directory of this distribution.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

extern crate term ;
// extern crate system as sys ;

// use std::sync::{ RwLock } ;
use std::sync::mpsc::Sender ;
// use std::collections::HashMap ;

use term::{
  Offset, Term, Sym, Factory
} ;

// pub type InvariantSet = RwLock<HashMap<Sym, Term>> ;

// pub type Cex = HashMap<(Var, Offset), Cst> ;

/** Message from kino to the techniques. */
pub enum MsgDown {
  Invariants(Sym, Vec<Term>),
  Forget(Sym),
}

/** Enumerates the techniques. */
#[derive(Debug, Clone, Copy)]
pub enum Technique {
  /** Bounded model checking. */
  Bmc,
  /** Induction. */
  Ind,
}
impl Technique {
  /** A string representation of a technique. */
  pub fn to_str(& self) -> & str {
    use Technique::* ;
    match * self {
      Bmc => "bmc",
      Ind => "ind",
    }
  }
}

/** Info a technique can communicate. */
pub enum Info {
  At(Offset)
}

/** Message from the techniques to kino. */
pub enum MsgUp {
  /** Invariants discovered. */
  Invariants,
  /** Not implemented. */
  Inimplemented,
  /** Log message. */
  Bla(Technique, String),
  /** Some properties were proved. */
  Proved(Vec<Sym>, Technique, Info),
  /** Some properties were falsified. */
  Disproved(Vec<Sym>, Technique, Info),
}

/** Used by the techniques to communicate with kino. */
pub struct Event {
  /** Sender to kin, */
  r: Sender<MsgUp>,
  /** Identifier of the technique. */
  t: Technique,
  /** Term factory. */
  f: Factory,
}
impl Event {
  /** Creates a new `Event`. */
  pub fn mk(r: Sender<MsgUp>, t: Technique, f: Factory) -> Self {
    Event { r: r, t: t, f: f }
  }
  /** Sends a proved message upwards. */
  pub fn proved(& self, props: Vec<Sym>, info: Info) {
    self.r.send(
      MsgUp::Proved(props, self.t, info)
    ).unwrap()
  }
  /** Sends a falsification message upwards. */
  pub fn disproved(& self, props: Vec<Sym>, info: Info) {
    self.r.send(
      MsgUp::Disproved(props, self.t, info)
    ).unwrap()
  }
  /** Sends a log message upwards. */
  pub fn log(& self, s: & str) {
    self.r.send(
      MsgUp::Bla(self.t, s.to_string())
    ).unwrap()
  }
  /** The factory in an `Event`. */
  pub fn factory(& self) -> & Factory {
    & self.f
  }
}



// pub struct EventBuilder {
//   r: Sender<MsgUp>,
// }
// impl EventBuilder {
//   pub fn mk(r: Sender<MsgUp>) -> Self { EventBuilder { r: r } }
//   pub fn event(self, t: Technique) -> Event { Event::mk(self.r, t) }
// }

