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

use std::sync::{ RwLock } ;
use std::sync::mpsc::Sender ;
use std::collections::HashMap ;

use term::{
  Offset, Term, Sym, Var, Cst, Factory
} ;

// use sys::Prop ;

pub type InvariantSet = RwLock<HashMap<Sym, Term>> ;

pub type Cex = HashMap<(Var, Offset), Cst> ;

pub enum MsgDown {
  Invariants(Sym, Vec<Term>),
  Forget(Sym),
}

#[derive(Debug, Clone, Copy)]
pub enum Technique {
  Bmc,
  Ind,
}
impl Technique {
  pub fn to_str(& self) -> & str {
    use Technique::* ;
    match * self {
      Bmc => "bmc",
      Ind => "ind",
    }
  }
}

pub enum Info {
  At(Offset)
}

pub enum MsgUp {
  Invariants,
  Inimplemented,
  Bla(Technique, String),
  Proved(Vec<Sym>, Technique, Info),
  Disproved(Vec<Sym>, Technique, Info),
}

pub struct Event {
  r: Sender<MsgUp>,
  t: Technique,
  f: Factory,
}
impl Event {
  pub fn mk(r: Sender<MsgUp>, t: Technique, f: Factory) -> Self {
    Event { r: r, t: t, f: f }
  }
  pub fn proved(& self, props: Vec<Sym>, info: Info) {
    self.r.send(
      MsgUp::Proved(props, self.t, info)
    ).unwrap()
  }
  pub fn disproved(& self, props: Vec<Sym>, info: Info) {
    self.r.send(
      MsgUp::Disproved(props, self.t, info)
    ).unwrap()
  }
  pub fn log(& self, s: & str) {
    self.r.send(
      MsgUp::Bla(self.t, s.to_string())
    ).unwrap()
  }
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

