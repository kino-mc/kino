// Copyright 2015 Adrien Champion. See the COPYRIGHT file at the top-level
// directory of this distribution.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

/*! Messages from kino to techniques and back. */

use std::fmt ;
use std::thread ;
use std::sync::mpsc ;
use std::sync::mpsc::{ Sender, Receiver, TryRecvError } ;
use std::collections::HashMap ;

use term::{
  Offset, Sym, Factory, Model, STerm
} ;

use sys::{ Prop, Sys } ;

use ::{ Technique, CanRun } ;

/** Wrapper around master and kids receive and send channels. */
pub struct KidManager {
  /** Receives messages from kids. */
  r: mpsc::Receiver<MsgUp>,
  /** Sends messages to master. */
  s: mpsc::Sender<MsgUp>,
  /** Senders to running techniques. */
  senders: HashMap<Technique, mpsc::Sender<MsgDown>>,
}
impl KidManager {
  /** Constructs a kid manager. */
  pub fn mk() -> Self {
    let (sender, receiver) = mpsc::channel() ;
    KidManager { r: receiver, s: sender, senders: HashMap::new() }
  }
  /** Launches a technique. */
  pub fn launch<T: CanRun + Send + 'static>(
    & mut self, t: T, sys: Sys, props: Vec<Prop>, f: & Factory
  ) -> Result<(), String> {
    let (s,r) = mpsc::channel() ;
    let id = t.id().clone() ;
    let event = Event::mk(
      self.s.clone(), r, t.id().clone(), f.clone(), & props
    ) ;
    match thread::Builder::new().name(id.thread_name()).spawn(
      move || t.run(sys, props, event)
    ) {
      Ok(_) => (),
      Err(e) => return Err(
        format!("could not spawn process {}:\n{}", id.desc(), e)
      ),
    } ;
    match self.senders.insert(id, s) {
      None => Ok(()),
      Some(_) => Err(
        format!("technique {} is already running", id.to_str())
      ),
    }
  }

  /** Broadcasts a message to the kids. */
  #[inline(always)]
  pub fn broadcast(& self, msg: MsgDown) {
    for (_, sender) in self.senders.iter() {
      match sender.send(msg.clone()) {
        Ok(()) => (),
        // Should do something here.
        // This happens when the techniques already exited.
        Err(_) => (),
      }
    }
  }

  /** Receive a message from the kids. */
  #[inline(always)]
  pub fn recv(& self) -> Result<MsgUp, mpsc::RecvError> {
    self.r.recv()
  }
  /** Forget a kid. */
  #[inline(always)]
  pub fn forget(& mut self, t: & Technique) {
    match self.senders.remove(t) {
      Some(_) => (),
      None => panic!("[kid_manager.forget] did not know {}", t.to_str()),
    }
  }
  /** True iff there's no more kids known by the manager. */
  #[inline(always)]
  pub fn kids_done(& self) -> bool { self.senders.is_empty() }
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

/** Message from kino to the techniques. */
#[derive(Debug,Clone)]
pub enum MsgDown {
  /** Contains invariants for a system. */
  Invariants(Sym, Vec<STerm>),
  /** Some properties have been proved or disproved. */
  Forget(Vec<Sym>),
  /** Some properties were found k-true. */
  KTrue(Vec<Sym>, Offset),
}

/** Message from the techniques to kino. */
pub enum MsgUp {
  /** Invariants discovered. */
  Invariants,
  /** Not implemented. */
  Unimplemented,
  /** Technique is done. */
  Done(Technique, Info),
  /** Log message. */
  Bla(Technique, String),
  /** Error message. */
  Error(Technique, String),
  /** Warning message. */
  Warning(Technique, String),
  /** KTrue. */
  KTrue(Vec<Sym>, Technique, Offset),
  /** Some properties were proved. */
  Proved(Vec<Sym>, Technique, Info),
  /** Some properties were falsified. */
  Disproved(Model, Vec<Sym>, Technique, Info),
}
impl fmt::Display for MsgUp {
  fn fmt(& self, fmt: & mut fmt::Formatter) -> fmt::Result {
    use msg::MsgUp::* ;
    match * self {
      Invariants => write!(fmt, "Invariants"),
      Unimplemented => write!(fmt, "Unimplemented"),
      Done(ref t, _) => write!(fmt, "Done({})", t),
      Bla(ref t, _) => write!(fmt, "Bla({})", t),
      Error(ref t, _) => write!(fmt, "Error({})", t),
      Warning(ref t, _) => write!(fmt, "Warning({})", t),
      KTrue(_, ref t, _) => write!(fmt, "KTrue({})", t),
      Proved(_, ref t, _) => write!(fmt, "Proved({})", t),
      Disproved(_, _, ref t, _) => write!(fmt, "Disproved({})", t),
    }
  }
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
  /** Sends an error upwards. */
  pub fn error(& self, s: & str) {
    self.s.send(
      MsgUp::Error(self.t, s.to_string())
    ).unwrap()
  }
  /** Sends a warning upwards. */
  pub fn warning(& self, s: & str) {
    self.s.send(
      MsgUp::Warning(self.t, s.to_string())
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