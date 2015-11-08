#![allow(non_upper_case_globals)]
#![warn(missing_docs)]
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

use event::Technique ;

static header: & 'static str = "|=====| " ;
static trailer: & 'static str = "|=====|" ;
static prefix: & 'static str = "| " ;

struct Log {
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
  fn error_line(& self, s: & str) {
    println!("{}  {}", self.error_style.paint(prefix), s)
  }
  fn print(& self, s: & str) {
    println!("{}{}", prefix, s)
  }
  fn log(& self, t: Technique, bla: String) {
    println!("{}{}:", prefix, self.bold.paint(t.to_str())) ;
    for line in bla.lines() {
      println!("{}  {}", prefix, line)
    } ;
    self.space()
  }
}

fn launch(
  log: & Log, c: & Context, sys: Sys, props: Vec<Prop>, _: Option<Vec<Term>>
) -> Result<(Sys, HashMap<Sym, Term>), ()> {
  use event::{ MsgUp, Event } ;
  use event::MsgUp::* ;
  log.title("Running") ;
  log.space() ;

  log.print("creating channel") ;
  let (sender, receiver) = mpsc::channel::<MsgUp>() ;

  // Launch BMC.
  log.print("spawning bmc") ;
  let factory = c.factory().clone() ;
  thread::spawn(
    move || bmc::run(
      sys, props.clone(), Event::mk(
        sender, Technique::Bmc, factory
      )
    )
  ) ;

  log.print("entering receive loop") ;
  log.space() ;

  loop {
    match receiver.recv() {
      Ok( Bla(from, bla) ) => log.log(from, bla),
      Ok(_) => log.print("received event"),
      Err(e) => {
        log.error() ;
        log.error_line( & format!("{}", e) ) ;
        break
      },
    }
  }

  log.space() ;
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
