#![allow(non_upper_case_globals)]
#![deny(missing_docs)]
// Copyright 2015 Adrien Champion. See the COPYRIGHT file at the top-level
// directory of this distribution.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

/*! Main project for kinō.

## To do:

write stuff here
*/

extern crate nom ;
extern crate term ;
extern crate system as sys ;
extern crate event ;
extern crate bmc ;
extern crate kind ;

use std::collections::HashMap ;
use std::sync::mpsc ;
use std::thread ;

use term::{ Sym, Term } ;

use sys::{ Prop, Sys } ;
use sys::ctxt::* ;

use event::{ CanRun, Technique } ;
use event::Technique::Kino ;
use event::log::{ MasterLog, Formatter, Styler } ;
use event::msg::{ MsgUp, MsgDown, Event, Info } ;

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
    & mut self, t: T, sys: Sys, props: Vec<Prop>, f: & term::Factory
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

fn launch<F: Formatter, S: Styler>(
  log: & MasterLog<F,S>,
  c: & Context, sys: Sys, props: Vec<Prop>, _: Option<Vec<Term>>
) -> Result<(Sys, HashMap<Sym, Term>), ()> {
  use event::msg::MsgUp::* ;
  use std::io::Write ;
  log.title( & format!("Running on {}", sys.sym().sym()) ) ;
  log.nl() ;

  let mut manager = KidManager::mk() ;

  match manager.launch(
    bmc::Bmc, sys.clone(), props.clone(), c.factory()
  ) {
    Ok(()) => (),
    Err(s) => { log.sad(& Kino, & s) ; return Err(()) },
  } ;
  match manager.launch(
    kind::KInd, sys.clone(), props.clone(), c.factory()
  ) {
    Ok(()) => (),
    Err(s) => { log.sad(& Kino, & s) ; return Err(()) },
  } ;

  // let mut bytes = Vec::<u8>::new() ;
  // sys.init().2.to_smt2(& mut bytes, & Offset2::init()) ;
  // let init = ::std::str::from_utf8(& bytes).unwrap() ;
  // let mut bytes = Vec::<u8>::new() ;
  // sys.trans().2.to_smt2(& mut bytes, & Offset2::init()) ;
  // let trans = ::std::str::from_utf8(& bytes).unwrap() ;
  // log.master_log(
  //   format!("system:\ninit:\n  {}\ntrans:\n  {}", init, trans)
  // ) ;

  // log.title("") ;
  // log.space() ;

  loop {
    if manager.kids_done() { break } ;

    match manager.recv() {

      Ok( Bla(from, bla) ) => log.log(& from, & bla),

      Ok( Error(from, bla) ) => log.sad(& from, & bla),

      Ok( Disproved(model, props, from, _) ) => {
        // let mut s = "model:".to_string() ;
        // for & ( (ref var, ref off), ref val ) in model.iter() {
        //   match * off {
        //     None => s = format!("{}\n{} -> {}", s, var, val),
        //     Some(ref o) => s = format!("{}\n{}@{} -> {}", s, var, o, val),
        //   }
        // } ;
        // log.master_log(s) ;
        let cex = c.cex_of(& model, & sys) ;
        log.log_cex(& from, & cex, & props) ;
        manager.broadcast( MsgDown::Forget(props) )
      },

      Ok( Proved(props, from, info) ) => {
        log.log_proved(& from, & props, & info) ;
        let mut vec = Vec::with_capacity(props.len()) ;
        for prop in props.iter() {
          match c.get_prop(prop) {
            None => panic!("[kino.proved] unknown property {}", prop),
            Some(ref prop) => vec.push(prop.body().clone()),
          }
        } ;
        manager.broadcast( MsgDown::Forget(props) ) ;
        manager.broadcast( MsgDown::Invariants(sys.sym().clone(), vec) )
      },

      Ok( KTrue(props, _, o) ) => {
        // if props.len() > 1 {
        //   let mut s = format!("true up to {}:", o) ;
        //   for prop in props.iter() {
        //     s = format!("{}\n{}", s, prop)
        //   } ;
        //   log.log(from, s) ;
        // } else {
        //   assert!(props.len() == 1) ;
        //   log.log(from, format!("{} is true up to {}", props[0], o))
        // } ;
        manager.broadcast( MsgDown::KTrue(props,o) )
      },

      Ok( Done(from, Info::At(_)) ) => {
        manager.forget(& from)
      },

      Ok( Done(from, info) ) => {
        log.log(& from, & format!("done {}", info)) ;
        manager.forget(& from)
      },

      Ok( msg ) => log.bad(
        & Kino, & format!("unknown message {}", msg)
      ),

      Err(e) => {
        log.bad(& Kino, & format!("{:?}", e)) ;
        break
      },
    }
  }

  log.trail() ;
  Err(())
}

fn main() {
  use std::fs::File ;
  use std::env::args ;

  let log = MasterLog::default() ;

  log.sep() ;
  log.sep() ;

  let mut args = args() ;
  args.next().unwrap() ;

  for file in args {
    let factory = term::Factory::mk() ;
    let mut context = Context::mk(factory, 10000) ;

    log.title( & format!("opening \"{}\"", file) ) ;
    match File::open(& file) {
      Ok(mut f) => {
        log.print( & log.mk_happy("success") ) ;
        log.title("parsing") ;
        match context.read(& mut f) {
          Ok(res) => {
            log.print( & log.mk_happy("success") ) ;

            log.title("Context") ;
            for line in context.lines().lines() {
              log.print(line)
            } ;

            log.title("Query") ;
            for line in res.lines().lines() {
              log.print(line)
            } ;

            match res {
              Res::Exit => (),
              Res::Check(sys, props) => {
                log.trail() ;
                let _ = launch(& log, & context, sys, props, None) ;
              },
              Res::CheckAss(_, _, _) => {
                log.bad(
                  & Kino, "verify with assumption is not supported"
                ) ;
                log.trail()
              },
            }
          },
          Err( e ) => {
            log.bad( & Kino, & format!("{}", e) ) ;
            log.trail()
          },
        }
      },
      Err(e) => {
        log.bad( & Kino, & format!("{}", e) ) ;
        log.trail()
      },
    } ;

    log.sep()
  }
  ()
}
