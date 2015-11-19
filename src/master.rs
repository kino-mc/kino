// Copyright 2015 Adrien Champion. See the COPYRIGHT file at the top-level
// directory of this distribution.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

/*! The Master is kino's top level.

It runs on a system and tries to prove some properties. */

use std::io::Write ;
use std::collections::HashMap ;

use term::{ Sym, Term } ;

use system::{ Prop, Sys } ;
use system::ctxt::* ;

use event::Technique::Kino ;
use event::msg::MsgUp::* ;
use event::msg::{ KidManager, MsgDown, Info } ;
use event::log::{ MasterLog, Formatter, Styler } ;

use bmc ;
use kind ;

/** Master, handles all the underlying techniques running in parallel. */
pub struct Master ;
impl Master {
  /** Launches the master and all the techniques specified to try to prove that
  `props` are invariants for `sys`.*/
  pub fn launch<F: Formatter, S: Styler>(
    log: & MasterLog<F,S>, c: & Context,
    sys: Sys, props: Vec<Prop>, _assumptions: Option<Vec<Term>>
  ) -> Result<(Sys, HashMap<Sym, Term>), ()> {

    log.title( & format!("Running on {}", sys.sym().sym()) ) ;
    log.nl() ;

    // Creating manager for techniques.
    let mut manager = KidManager::mk() ;

    // Launching BMC.
    match manager.launch(
      bmc::Bmc, sys.clone(), props.clone(), c.factory()
    ) {
      Ok(()) => (),
      Err(s) => { log.bad(& Kino, & s) ; return Err(()) },
    }

    // Launching k-induction.
    match manager.launch(
      kind::KInd, sys.clone(), props.clone(), c.factory()
    ) {
      Ok(()) => (),
      Err(s) => { log.bad(& Kino, & s) ; return Err(()) },
    }

    // Entering message loop.
    loop {
      // Stopping if no more kids running.
      if manager.kids_done() { break } ;

      // Receiving a message.
      match manager.recv() {

        Ok( Bla(from, bla) ) => log.log(& from, & bla),

        Ok( Error(from, bla) ) => log.bad(& from, & bla),

        Ok( Warning(from, bla) ) => log.sad(& from, & bla),

        Ok( Disproved(model, props, from, _) ) => {
          let cex = c.cex_of(& model, & sys) ;
          log.log_cex(& from, & cex, & props) ;
          manager.broadcast( MsgDown::Forget(props) ) ;
        },

        Ok( Proved(props, from, info) ) => {
          log.log_proved(& from, & props, & info) ;
          let mut vec = Vec::with_capacity(props.len()) ;
          for prop in props.iter() {
            match c.get_prop(prop) {
              None => panic!("[kino.proved] unknown property {}", prop),
              Some(ref prop) => vec.push( prop.body().clone() ),
            }
          } ;
          manager.broadcast( MsgDown::Forget(props) ) ;
          manager.broadcast( MsgDown::Invariants(sys.sym().clone(), vec) ) ;
        },

        Ok( KTrue(props, _, o) ) => manager.broadcast(
          MsgDown::KTrue(props, o)
        ),

        Ok( Done(from, Info::At(_)) ) => manager.forget(& from),

        Ok( Done(from, info) ) => {
          log.log(& from, & format!("done {}", info)) ;
          manager.forget(& from)
        },

        Ok( msg ) => log.bad( & Kino, & format!("unknown message {}", msg) ),

        Err(e) => {
          log.bad(& Kino, & format!("{:?}", e)) ;
          break
        },

      }
    } ;

    log.trail() ;

    Err(())

  }
}