#![allow(non_upper_case_globals)]
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

extern crate ansi_term as ansi ;
extern crate nom ;
extern crate rsmt2 ;
extern crate term ;
extern crate system as sys ;
extern crate event ;
extern crate bmc ;
extern crate kind ;

/** Provides access to the documentation of the sub projects and main
libraries. */
pub mod subs {
  /** `rsmt2` library documentation. */
  pub use ::rsmt2 as smt ;
  /** `term` sub-project documentation. */
  pub use ::term ;
  /** `system` sub-project documentation. */
  pub use ::sys ;
  /** `event` sub-project documentation. */
  pub use ::event ;
}

use std::collections::HashMap ;
use std::sync::mpsc ;
use std::thread ;

use ansi::{ ANSIString, Style, Colour } ;

use term::{ Sym, Term } ;

use sys::{ Prop, Sys } ;
use sys::ctxt::* ;

use event::{ MsgUp, MsgDown, CanRun, Technique, Event } ;

static header: & 'static str = "|=====| " ;
static trailer: & 'static str = "|=====|" ;
static prefix: & 'static str = "| " ;

pub struct Log {
  pub bold: Style,
  pub success_style: Colour,
  pub success: ANSIString<'static>,
  pub error_style: Style,
  pub error: ANSIString<'static>,
}
impl Log {
  fn mk() -> Self {
    let bold = ansi::Style::new().bold() ;
    let success_style = ansi::Colour::Green ;
    let success = success_style.paint("success") ;
    let error_style = ansi::Colour::Red.bold() ;
    let error = error_style.paint("error:") ;
    Log {
      bold: bold,
      success_style: success_style,
      success: success,
      error_style: error_style,
      error: error,
    }
  }
  fn space(& self) { println!("{}", prefix) }
  fn empty_space(& self) { println!("") }
  fn trail(& self) {
    println!("{}", trailer) ;
    println!("")
  }
  fn title(& self, e: & str) {
    println!("{}{}", header, self.bold.paint(e))
  }
  fn success(& self) {
    println!("{}{}", self.success_style.paint(prefix), self.success)
  }
  fn error(& self) {
    println!("{}{}", self.error_style.paint(prefix), self.error)
  }
  fn error_from(& self, t: Technique) {
    println!(
      "{}{} in {}",
      self.error_style.paint(prefix), self.error, self.bold.paint(t.to_str())
    )
  }
  fn error_line(& self, s: & str) {
    println!("{}  {}", self.error_style.paint(prefix), s)
  }
  fn print(& self, s: & str) {
    println!("{}{}", prefix, s)
  }
  fn log(& self, t: Technique, bla: String) {
    let mut lines = bla.lines() ;
    println!(
      "{}{}: {}",
      prefix, self.bold.paint(t.to_str()), lines.next().unwrap()
    ) ;
    for line in lines {
      println!("{}   {}", prefix, line)
    } ;
    self.space()
  }
  fn master_log(& self, bla: String) {
    let mut lines = bla.lines() ;
    println!(
      "{}{}: {}",
      prefix, self.success_style.paint("kino"), lines.next().unwrap()
    ) ;
    for line in lines {
      println!("{}   {}", prefix, line)
    } ;
    self.space()
  }
}

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
    & mut self, log: & Log,
    t: T, sys: Sys, props: Vec<Prop>, f: & term::Factory
  ) {
    log.master_log(
      format!("spawning {}", t.id().to_str())
    ) ;
    let (s,r) = mpsc::channel() ;
    let id = t.id().clone() ;
    let event = Event::mk(
      self.s.clone(), r, t.id().clone(), f.clone(), & props
    ) ;
    thread::spawn( move || t.run(sys, props, event) ) ;
    match self.senders.insert(id, s) {
      None => (),
      Some(_) => {
        log.error() ;
        log.error_line(
          & format!("technique {} is already running", id.to_str())
        )
      },
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

fn launch(
  log: & Log, c: & Context, sys: Sys, props: Vec<Prop>, _: Option<Vec<Term>>
) -> Result<(Sys, HashMap<Sym, Term>), ()> {
  use event::MsgUp::* ;
  log.title("Running") ;
  log.space() ;

  let mut manager = KidManager::mk() ;

  manager.launch(
    log, bmc::Bmc, sys.clone(), props.clone(), c.factory()
  ) ;
  manager.launch(
    log, kind::KInd, sys.clone(), props.clone(), c.factory()
  ) ;

  // log.master_log("entering receive loop".to_string()) ;
  log.title("") ;
  log.space() ;

  loop {
    if manager.kids_done() { break } ;

    match manager.recv() {

      Ok( Bla(from, bla) ) => log.log(from, bla),

      Ok( Error(from, bla) ) => {
        log.error_from(from) ;
        for line in bla.lines() {
          log.error_line(line)
        } ;
        log.space()
      },

      Ok( Disproved(props, from, info) ) => {
        if props.len() > 1 {
          let mut s = format!(
            "falsified {} properties {}", props.len(), info
          ) ;
          for prop in props.iter() {
            s = format!("{}\n{}", s, prop)
          } ;
          log.log(from, s)
        } else {
          assert!(props.len() == 1) ;
          log.log(from, format!("falsified {} {}", props[0], info))
        } ;
        manager.broadcast( MsgDown::Forget(props) )
      },

      Ok( Proved(props, from, info) ) => {
        if props.len() > 1 {
          let mut s = format!(
            "proved {} properties {}", props.len(), info
          ) ;
          for prop in props.iter() {
            s = format!("{}\n  {}", s, prop)
          } ;
          log.log(from, s)
        } else {
          assert!(props.len() == 1) ;
          log.log(from, format!("proved {} {}", props[0], info))
        } ;
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

      Ok( Done(from, info) ) => {
        log.log(
          from,
          format!("done {}", info)
        ) ;
        manager.forget(& from)
      },

      Ok( _ ) => log.master_log("received a message".to_string()),

      Err(e) => {
        log.error() ;
        for line in (format!("{:?}", e)).lines() {
          log.error_line(line)
        } ;
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

  let log = Log::mk() ;

  log.empty_space() ;
  log.empty_space() ;

  let mut args = args() ;
  args.next().unwrap() ;

  for file in args {
    let factory = term::Factory::mk() ;
    let mut context = Context::mk(factory, 10000) ;

    log.title( & format!("opening \"{}\"", file) ) ;
    match File::open(& file) {
      Ok(mut f) => {
        log.success() ;
        log.title("parsing") ;
        match context.read(& mut f) {
          Ok(res) => {
            log.success() ;

            log.title("Context") ;
            for line in context.lines().lines() {
              log.print(line)
            } ;

            log.title("Query") ;
            for line in res.lines().lines() {
              log.print(line)
            } ;
            log.trail() ;

            match res {
              Res::Exit => (),
              Res::Check(sys, props) => {
                let _ = launch(& log, & context, sys, props, None) ;
              },
              Res::CheckAss(sys, props, ass) => {
                let _ = launch(& log, & context, sys, props, Some(ass)) ;
              },
            }
          },
          Err( e ) => {
            log.space() ;
            log.error() ;
            for line in ( format!("{}", e) ).lines() {
              log.error_line(line)
            } ;
            log.trail()
          },
        }
      },
      Err(e) => {
        log.space() ;
        log.error() ;
        for line in ( format!("{}", e) ).lines() {
          log.error_line(line)
        } ;
        log.trail()
      },
    } ;

    log.empty_space()
  }
  ()
}
