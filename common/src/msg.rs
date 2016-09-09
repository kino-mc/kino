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

use std::sync::Arc ;

use term::{
  Offset, Sym, Factory, Model, STermSet
} ;

use sys::{ Prop, Sys } ;

use ::{ Tek, CanRun, Res } ;

/// Wrapper around master and kids receive and send channels.
pub struct KidManager {
  /// Receives messages from kids.
  r: Receiver<MsgUp>,
  /// Sends messages to master.
  s: Sender<MsgUp>,
  /// Senders to running techniques.
  senders: HashMap<Tek, mpsc::Sender<MsgDown>>,
}
impl KidManager {
  /// Constructs a kid manager.
  pub fn mk() -> Self {
    let (sender, receiver) = mpsc::channel() ;
    KidManager { r: receiver, s: sender, senders: HashMap::new() }
  }
  /// Launches a technique.
  pub fn launch<
    Conf: 'static + Sync + Send, T: CanRun<Conf> + Send + 'static
  >(
    & mut self, t: T, sys: Sys, props: Vec<Prop>, f: & Factory, conf: Arc<Conf>
  ) -> Result<(), String> {
    let (s,r) = mpsc::channel() ;
    let id = t.id().clone() ;
    let event = Event::mk(
      self.s.clone(), r, t.id().clone(), f.clone(), & props
    ) ;
    match thread::Builder::new().name(id.thread_name()).spawn(
      move || t.run(conf, sys, props, event)
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

  /// Broadcasts a message to the kids.
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

  /// Receive a message from the kids.
  #[inline(always)]
  pub fn recv(& self) -> Result<MsgUp, mpsc::RecvError> {
    self.r.recv()
  }
  /// Forget a kid.
  #[inline(always)]
  pub fn forget(& mut self, t: & Tek) -> Res<()> {
    try_str_opt!(
      self.senders.remove(t),
      "[KidManager::forget] No instance of {} running", t.to_str()
    ) ;
    Ok(())
  }
  /// True iff there's no more kids known by the manager.
  #[inline(always)]
  pub fn kids_done(& self) -> bool { self.senders.is_empty() }

  /// Sends a pruning message if a pruner is registered. Returns `true` iff the
  /// pruning message was successfully sent.
  ///
  /// If the pruner is registered but the message can't be sent, writes a `bad`
  /// message explaining what happened, forgets the pruner, and returns
  /// `false`.
  #[inline(always)]
  pub fn prune_if_possible<BadLog: Fn(& str)>(
    & mut self, tek: Tek, sys: Sym, invs: STermSet, info: Option<usize>,
    bad_log: BadLog
  ) -> bool {
    let send_res = if let Some(pruner) = self.senders.get(& Tek::Pruner) {
      pruner.send(
        MsgDown::InvariantPruning( tek, sys.clone(), invs.clone(), info )
      )
    } else {
      return false
    } ;
    // Not reachable if pruner's not registered, see early return above.
    match send_res {
      Ok(()) => true,
      Err(e) => {
        bad_log(
          & format!(
            "could not send pruning job:\n\
            {}\n\
            pruner seems to be dead, forgetting it", e
          )
        ) ;
        match self.senders.remove(& Tek::Pruner) {
          _ => false,
        }
      },
    }
  }
}



/// Info a technique can communicate.
pub enum Info {
  /// Typical techniques unroll the system, this communicates the number of
  /// unrollings.
  At(Offset),
  /// An error occurred.
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

/// Status of a property.
#[derive(Debug, Clone)]
pub enum Status {
  /// Property was proved.
  Proved,
  /// Property was disproved.
  Disproved,
}

/// Message from kino to the techniques.
#[derive(Debug, Clone)]
pub enum MsgDown {
  /// Contains invariants for a system.
  Invariants(Sym, STermSet),
  /// Invariant pruning job.
  InvariantPruning(Tek, Sym, STermSet, Option<usize>),
  /// Some properties have been proved or disproved.
  Forget(Vec<Sym>, Status),
  /// Some properties were found k-true.
  KTrue(Vec<Sym>, Offset),
}

/// Message from the techniques to kino.
pub enum MsgUp {
  /// Invariants discovered.
  ///
  /// Stores
  /// - the technique who discovered the invariants
  /// - system's name
  /// - invariant set
  /// - optional invariant discovery info (unrolling, typically)
  Invariants(Tek, Sym, STermSet, Option<usize>),
  /// Invariants discovered after pruning.
  ///
  /// Stores
  /// - the technique responsible for pruning
  /// - the technique who discovered the invariants
  /// - system's name
  /// - pruned invariant set
  /// - number of invariants in the original set
  /// - optional invariant discovery info (unrolling, typically)
  PrunedInvariants(Tek, Tek, Sym, STermSet, usize, Option<usize>),
  /// Not implemented.
  Unimplemented,
  /// Log message.
  Bla(Tek, String),
  /// Warning message.
  Warning(Tek, String),
  /// Error message.
  Error(Tek, String),
  /// Tek is done.
  Done(Tek, Info),
  /// KTrue.
  KTrue(Tek, Vec<Sym>, Tek, Offset),
  /// Some properties were proved.
  Proved(Vec<Sym>, Tek, Offset),
  /// Some properties were falsified.
  Disproved(Model, Vec<Sym>, Tek, Info),
}
impl fmt::Display for MsgUp {
  fn fmt(& self, fmt: & mut fmt::Formatter) -> fmt::Result {
    use msg::MsgUp::* ;
    match * self {
      Invariants(ref t, ref sym, ref invs, ref at) => {
        try!(
          write!(
            fmt, "Invariants[{}{}]({},",
            sym,
            if let Some(at) = * at {
              format!(" at {}", at)
            } else {
              format!("")
            },
            t
          )
        ) ;
        for inv in invs {
          try!( write!(fmt, " {}", inv) )
        }
        write!(fmt, " )")
      },
      PrunedInvariants(
        ref t_p, ref t, ref sym, ref invs, ref card, ref at
      ) => {
        try!(
          write!(
            fmt, "Invariants[{}{}]({} by {} thru {},",
            sym,
            if let Some(at) = * at {
              format!(" at {}", at)
            } else {
              format!("")
            },
            card, t, t_p
          )
        ) ;
        for inv in invs {
          try!( write!(fmt, " {}", inv) )
        }
        write!(fmt, " )")
      },
      Unimplemented => write!(fmt, "Unimplemented"),
      Done(ref t, _) => write!(fmt, "Done({})", t),
      Bla(ref t, _) => write!(fmt, "Bla({})", t),
      Error(ref t, _) => write!(fmt, "Error({})", t),
      Warning(ref t, _) => write!(fmt, "Warning({})", t),
      KTrue(_, _, ref t, _) => write!(fmt, "KTrue({})", t),
      Proved(_, ref t, _) => write!(fmt, "Proved({})", t),
      Disproved(_, _, ref t, _) => write!(fmt, "Disproved({})", t),
    }
  }
}

/// Exits with code `0`.
fn exit<T>(_: T) {
  use std::process::exit ;
  exit(0)
}

/// Used by the techniques to communicate with kino.
pub struct Event {
  /// Sender to kino.
  s: Sender<MsgUp>,
  /// Receiver from kino.
  r: Receiver<MsgDown>,
  /// Identifier of the technique.
  t: Tek,
  /// Term factory.
  f: Factory,
  /// K-true properties.
  k_true: HashMap<Sym, Option<Offset>>,
}
impl Event {
  /// Creates a new `Event`.
  pub fn mk(
    s: Sender<MsgUp>, r: Receiver<MsgDown>,
    t: Tek, f: Factory, props: & [Prop]
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

  /// Sends a pruned invariant message upwards.
  pub fn pruned_invariants(
    & self, tek: Tek, sys: & Sym, invs: STermSet, old_card: usize,
    info: Option<usize>
  ) {
    self.s.send(
      MsgUp::PrunedInvariants(self.t, tek, sys.clone(), invs, old_card, info)
    ).unwrap_or_else( exit )
  }

  /// Sends an invariant message upwards.
  pub fn invariants(& self, sys: & Sym, invs: STermSet) {
    self.s.send(
      MsgUp::Invariants(self.t, sys.clone(), invs, None)
    ).unwrap_or_else( exit )
  }
  /// Sends an invariant message upwards, with a notion of offset.
  pub fn invariants_at(& self, sys: & Sym, invs: STermSet, at: usize) {
    self.s.send(
      MsgUp::Invariants(self.t, sys.clone(), invs, Some(at))
    ).unwrap_or_else( exit )
  }

  /// Sends a done message upwards.
  pub fn done(& self, info: Info) {
    self.s.send(
      MsgUp::Done(self.t, info)
    ).unwrap_or_else( exit )
  }
  /// Sends a done message upwards.
  pub fn done_at(& self, o: & Offset) {
    self.done(Info::At(o.clone()))
  }
  /// Sends a proved message upwards.
  pub fn proved(& self, props: Vec<Sym>, info: Offset) {
    self.s.send(
      MsgUp::Proved(props, self.t, info)
    ).unwrap_or_else( exit )
  }
  /// Sends a proved message upwards.
  pub fn proved_at(& self, props: Vec<Sym>, o: & Offset) {
    self.proved(props, o.clone())
  }
  /// Sends a falsification message upwards.
  pub fn disproved(& self, model: Model, props: Vec<Sym>, info: Info) {
    self.s.send(
      MsgUp::Disproved(model, props, self.t, info)
    ).unwrap_or_else( exit )
  }
  /// Sends a falsification message upwards.
  pub fn disproved_at(& self, model: Model, props: Vec<Sym>, o: & Offset) {
    self.disproved(model, props, Info::At(o.clone()))
  }
  /// Sends some k-true properties.
  pub fn k_true(& self, props: Vec<Sym>, o: & Offset) {
    self.s.send(
      MsgUp::KTrue(self.t, props, self.t, o.clone())
    ).unwrap_or_else( exit )
  }
  /// Sends a log message upwards.
  pub fn log(& self, s: & str) {
    self.s.send(
      MsgUp::Bla(self.t, s.to_string())
    ).unwrap_or_else( exit )
  }
  /// Sends an error upwards.
  pub fn error(& self, s: & str) {
    self.s.send(
      MsgUp::Error(self.t, s.to_string())
    ).unwrap_or_else( exit )
  }
  /// Sends a warning upwards.
  pub fn warning(& self, s: & str) {
    self.s.send(
      MsgUp::Warning(self.t, s.to_string())
    ).unwrap_or_else( exit )
  }
  /// The factory in an `Event`.
  pub fn factory(& self) -> & Factory {
    & self.f
  }
  /// Returns the offset a property is k_true for.
  #[inline(always)]
  pub fn get_k_true(& self, p: & Sym) -> & Option<Offset> {
    match self.k_true.get(p) {
      Some(res) => res,
      None => panic!("[event.k_true] unknown property"),
    }
  }
  /// Receive messages from the master.
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