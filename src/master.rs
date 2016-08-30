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

use std::sync::Arc ;
use std::collections::{ HashSet, HashMap } ;

use term::{ Sym, Term } ;

use system::{ Prop, Sys } ;
use system::ctxt::Context ;

use common::Tek::Kino ;
use common::conf ;
use common::msg::MsgUp::* ;
use common::msg::{ KidManager, MsgDown, Info, Status } ;
use common::log::{ MasterLog, Formatter, Styler } ;

use bmc ;
use kind ;
use tig ;

/** Master, handles all the underlying techniques running in parallel. */
pub struct Master ;
impl Master {
  /** Launches the master and all the techniques specified to try to prove that
  `props` are invariants for `sys`.*/
  pub fn launch<F: Formatter, S: Styler>(
    log: & MasterLog<F,S>, c: & Context,
    sys: Sys, props: Vec<Prop>,
    _assumptions: Option<Vec<Term>>,
    conf: conf::Master
  ) -> Result<(Sys, HashMap<Sym, Term>), ()> {

    let mut proved_set = HashSet::with_capacity(props.len()) ;
    let mut disproved_set = HashSet::with_capacity(props.len()) ;

    log.title( & format!("Running on {}", sys.sym().sym()) ) ;
    log.nl() ;

    // Creating manager for techniques.
    let mut manager = KidManager::mk() ;

    // Launching BMC.
    match conf.bmc {
      None => (),
      Some(conf) => if * conf.is_on() {
        match manager.launch(
          bmc::Bmc, sys.clone(), props.clone(), c.factory(), Arc::new(conf)
        ) {
          Ok(()) => (),
          Err(s) => { log.bad(& Kino, & s) ; return Err(()) },
        }
      },
    } ;

    // Launching k-induction.
    match conf.kind {
      None => (),
      Some(conf) => if * conf.is_on() {
          match manager.launch(
          kind::KInd, sys.clone(), props.clone(), c.factory(), Arc::new(conf)
        ) {
          Ok(()) => (),
          Err(s) => { log.bad(& Kino, & s) ; return Err(()) },
        }
      },
    } ;

    // Launching invgen.
    match conf.tig {
      None => (),
      Some(conf) => if * conf.is_on() {
        match manager.launch(
          tig::Tig, sys.clone(), props.clone(), c.factory(), Arc::new(conf)
        ) {
          Ok(()) => (),
          Err(s) => { log.bad(& Kino, & s) ; return Err(()) },
        }
      },
    } ;

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
          for prop in props.iter() {
            let was_there = disproved_set.insert(prop.clone()) ;
            debug_assert!( ! was_there ) ;
            if proved_set.contains(prop) {
              log.bad(
                & from,
                & format!("disproved {}, but it was previously proved", prop)
              ) ;
              log.trail() ;
              return Err(())
            }
          }
          let cex = c.cex_of(& model, & sys) ;
          log.log_cex(& from, & cex, & props) ;
          manager.broadcast( MsgDown::Forget(props, Status::Disproved) ) ;
        },

        Ok( Proved(props, from, info) ) => {
          log.log_proved(& from, & props, & info) ;
          let mut vec = Vec::with_capacity(props.len()) ;
          for prop in props.iter() {
            match c.get_prop(prop) {
              None => panic!("[kino.proved] unknown property {}", prop),
              Some(ref prop) => vec.push( prop.body().clone() ),
            }
            let was_there = proved_set.insert(prop.clone()) ;
            debug_assert!( ! was_there ) ;
            if disproved_set.contains(prop) {
              log.bad(
                & from,
                & format!("proved {}, but it was previously disproved", prop)
              ) ;
              log.trail() ;
              return Err(())
            }
          } ;
          manager.broadcast( MsgDown::Forget(props, Status::Proved) ) ;
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

    if disproved_set.is_empty() {
      if proved_set.len() == props.len() {
        log.log_safe()
      } else {
        log.log_unknown(
          props.iter().filter_map(
            |prop| if ! proved_set.contains(
              prop.sym()
            ) && ! disproved_set.contains(
              prop.sym()
            ) {
              Some(prop.sym())
            } else {
              None
            }
          )
        )
      }
    } else {
      log.log_unsafe()
    }

    log.trail() ;

    Err(())

  }
}