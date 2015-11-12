#![deny(missing_docs)]
// Copyright 2015 Adrien Champion. See the COPYRIGHT file at the top-level
// directory of this distribution.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

/*! Messages, structures for receiving and sending messages. */

extern crate term ;
extern crate system as sys ;

use std::fmt ;
// use std::sync::{ RwLock } ;
use std::sync::mpsc::{ Sender, Receiver, TryRecvError } ;
use std::collections::HashMap ;

use term::{
  Offset, Term, Sym, Factory, Model
} ;

use sys::{ Prop, Sys } ;

// pub type InvariantSet = RwLock<HashMap<Sym, Term>> ;

// pub type Cex = HashMap<(Var, Offset), Cst> ;

/** Message from kino to the techniques. */
#[derive(Debug,Clone)]
pub enum MsgDown {
  /** Contains invariants for a system. */
  Invariants(Sym, Vec<Term>),
  /** Some properties have been proved or disproved. */
  Forget(Vec<Sym>),
  /** Some properties were found k-true. */
  KTrue(Vec<Sym>, Offset),
}

/** Trait the techniques should implement so that kino can call them in a
generic way. */
pub trait CanRun {
  /** The identifier of the technique. */
  fn id(& self) -> Technique ;
  /** Runs the technique. */
  fn run(& self, sys: Sys, props: Vec<Prop>, event: Event) ;
}

/** Enumeration of the techniques. */
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Technique {
  /** Bounded model checking. */
  Bmc,
  /** Induction. */
  KInd,
}
impl Technique {
  /** A short string representation of a technique. */
  #[inline(always)]
  pub fn to_str(& self) -> & str {
    use Technique::* ;
    match * self {
      Bmc => "bmc",
      KInd => "k-ind",
    }
  }
  /** A description of a technique. */
  #[inline(always)]
  pub fn desc(& self) -> & str {
    use Technique::* ;
    match * self {
      Bmc => "bounded model checking",
      KInd => "k-induction",
    }
  }
  /** Thread name for techniques. */
  #[inline(always)]
  pub fn thread_name(& self) -> String {
    use Technique::* ;
    match * self {
      Bmc => "kino_bmc".to_string(),
      KInd => "kino_k-induction".to_string(),
    }
  }
}

/** Info a technique can communicate. */
pub enum Info {
  /** Typical techniques unroll the system, this communicates the number of
  unrollings. */
  At(Offset),
  /** An error occurred. */
  Error,
}
impl fmt::Display for Info {
  fn fmt(& self, fmt: & mut fmt::Formatter) -> fmt::Result {
    match * self {
      Info::At(ref o) => write!(fmt, "at {}", o),
      Info::Error => write!(fmt, "error"),
    }
  }
}

/** Message from the techniques to kino. */
pub enum MsgUp {
  /** Invariants discovered. */
  Invariants,
  /** Not implemented. */
  Inimplemented,
  /** Technique is done. */
  Done(Technique, Info),
  /** Log message. */
  Bla(Technique, String),
  /** Error message. */
  Error(Technique, String),
  /** KTrue. */
  KTrue(Vec<Sym>, Technique, Offset),
  /** Some properties were proved. */
  Proved(Vec<Sym>, Technique, Info),
  /** Some properties were falsified. */
  Disproved(Model, Vec<Sym>, Technique, Info),
}

/** Used by the techniques to communicate with kino. */
pub struct Event {
  /** Sender to kino. */
  s: Sender<MsgUp>,
  /** Receiver from kino. */
  r: Receiver<MsgDown>,
  /** Identifier of the technique. */
  t: Technique,
  /** Term factory. */
  f: Factory,
  /** K-true properties. */
  k_true: HashMap<Sym, Option<Offset>>,
}
impl Event {
  /** Creates a new `Event`. */
  pub fn mk(
    s: Sender<MsgUp>, r: Receiver<MsgDown>,
    t: Technique, f: Factory, props: & [Prop]
  ) -> Self {
    let mut k_true = HashMap::with_capacity(props.len()) ;
    for prop in props {
      match k_true.insert(prop.sym().clone(), None) {
        None => (),
        Some(_) => unreachable!(),
      }
    } ;
    Event { s: s, r: r, t: t, f: f, k_true: k_true }
  }
  /** Sends a done message upwards. */
  pub fn done(& self, info: Info) {
    self.s.send(
      MsgUp::Done(self.t, info)
    ).unwrap()
  }
  /** Sends a done message upwards. */
  pub fn done_at(& self, o: & Offset) {
    self.done(Info::At(o.clone()))
  }
  /** Sends a proved message upwards. */
  pub fn proved(& self, props: Vec<Sym>, info: Info) {
    self.s.send(
      MsgUp::Proved(props, self.t, info)
    ).unwrap()
  }
  /** Sends a proved message upwards. */
  pub fn proved_at(& self, props: Vec<Sym>, o: & Offset) {
    self.proved(props, Info::At(o.clone()))
  }
  /** Sends a falsification message upwards. */
  pub fn disproved(& self, model: Model, props: Vec<Sym>, info: Info) {
    self.s.send(
      MsgUp::Disproved(model, props, self.t, info)
    ).unwrap()
  }
  /** Sends a falsification message upwards. */
  pub fn disproved_at(& self, model: Model, props: Vec<Sym>, o: & Offset) {
    self.disproved(model, props, Info::At(o.clone()))
  }
  /** Sends some k-true properties. */
  pub fn k_true(& self, props: Vec<Sym>, o: & Offset) {
    self.s.send(
      MsgUp::KTrue(props, self.t, o.clone())
    ).unwrap()
  }
  /** Sends a log message upwards. */
  pub fn log(& self, s: & str) {
    self.s.send(
      MsgUp::Bla(self.t, s.to_string())
    ).unwrap()
  }
  /** Sends a log message upwards. */
  pub fn error(& self, s: & str) {
    self.s.send(
      MsgUp::Error(self.t, s.to_string())
    ).unwrap()
  }
  /** The factory in an `Event`. */
  pub fn factory(& self) -> & Factory {
    & self.f
  }
  /** Returns the offset a property is k_true for. */
  #[inline(always)]
  pub fn get_k_true(& self, p: & Sym) -> & Option<Offset> {
    match self.k_true.get(p) {
      Some(res) => res,
      None => panic!("[event.k_true] unknown property"),
    }
  }
  /** Receive messages from the master. */
  pub fn recv(& mut self) -> Option<Vec<MsgDown>> {
    let mut vec = vec![] ;
    loop {
      match self.r.try_recv() {
        Ok( MsgDown::KTrue(props, o) ) => {
          for prop in props {
            self.k_true.insert(prop, Some(o)) ; ()
          }
        },
        Ok( msg ) => vec.push(msg),
        Err( TryRecvError::Empty ) => break,
        Err( TryRecvError::Disconnected ) => return None,
      }
    } ;
    Some(vec)
  }
}



// pub struct EventBuilder {
//   r: Sender<MsgUp>,
// }
// impl EventBuilder {
//   pub fn mk(r: Sender<MsgUp>) -> Self { EventBuilder { r: r } }
//   pub fn event(self, t: Technique) -> Event { Event::mk(self.r, t) }
// }

