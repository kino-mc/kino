// Copyright 2015 Adrien Champion. See the COPYRIGHT file at the top-level
// directory of this distribution.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! The Master is kino's top level.
//!
//! It runs on a system and tries to prove some properties.

use std::sync::Arc ;
use std::collections::HashMap ;

use term::{ Term, STermSet } ;

use system::{ Prop, Sys } ;
use system::ctxt::Context ;

use common::Tek::Kino ;
use common::conf ;
use common::msg::MsgUp::* ;
use common::msg::{ KidManager, MsgDown, Info, Status } ;
use common::log::{ MasterLog, Formatter, Styler } ;

use bmc ;
use kind ;
use twind ;
use tig ;
use pruner ;

/// If the result is an error, prints it using `bad`.
macro_rules! try_log {
  ($e:expr, $log:expr, $( $arg:expr ),+ ) => (
    match $e {
      Ok(()) => (),
      Err(e) => {
        let blah = format!( $($arg),+ ) ;
        $log.bad(
          & Kino, & format!("{}\n{}\nmoving on...", blah, e)
        )
      },
    }
  )
}
/// If the result is an error, prints it using `bad` and breaks.
macro_rules! try_log_run {
  ($e:expr, $log:expr, $run:expr, $( $arg:expr ),+ ) => (
    match $e {
      Ok(res) => res,
      Err(e) => {
        let blah = format!( $($arg),+ ) ;
        $log.bad(
          & Kino, & format!("{}\n{}\nmoving on...", blah, e)
        ) ;
        $run
      },
    }
  )
}

/// Master, handles all the underlying techniques running in parallel.
pub struct Master ;
impl Master {
  /// Launches the master and all the techniques specified to try to prove that
  /// `props` are invariants for `sys`.
  pub fn launch<F: Formatter, S: Styler>(
    log: & MasterLog<F,S>, c: & mut Context,
    sys: Sys, props: Vec<Prop>,
    _assumptions: Option<Vec<Term>>,
    conf: conf::Master
  ) -> Result<(), ()> {

    let mut invar_map = HashMap::new() ;
    invar_map.insert(sys.sym().clone(), STermSet::new()) ;
    for sub in sys.subsys_syms().into_iter() {
      invar_map.insert(sub, STermSet::new()) ; ()
    }

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

    // Launching 2-induction.
    match conf.twind {
      None => (),
      Some(conf) => if * conf.is_on() {
        match manager.launch(
          twind::Twind, sys.clone(), props.clone(), c.factory(), Arc::new(conf)
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

    // Launching invgen.
    match conf.pruner {
      None => (),
      Some(conf) => if * conf.is_on() {
        match manager.launch(
          pruner::Pruner, sys.clone(), props.clone(),
          c.factory(), Arc::new(conf)
        ) {
          Ok(()) => (),
          Err(s) => { log.bad(& Kino, & s) ; return Err(()) },
        }
      },
    } ;

    // Result returned when exting the loop.
    let mut result = Ok(()) ;

    // Entering message loop.
    'msg_loop: loop {
      // Stopping if no more kids running.
      if manager.kids_done() { break } ;
      // Stopping if no property left to prove.
      if ! try_log_run!(
        c.some_prop_unknown(& props), log, {
          result = Err(()) ;
          break 'msg_loop
        },
        "while checking for unknown properties"
      ) {
        break 'msg_loop
      }

      // Receiving a message.
      match manager.recv() {

        Ok( Bla(from, bla) ) => log.log(& from, & bla),

        Ok( Error(from, bla) ) => log.bad(& from, & bla),

        Ok( Warning(from, bla) ) => log.sad(& from, & bla),

        Ok( Disproved(model, props, from, _) ) => {
          let cex = c.cex_of(& model, & sys) ;
          for prop in props.iter() {
            try_log_run!(
              c.set_prop_false(prop, cex.clone()), log, {
                result = Err(()) ;
                break 'msg_loop
              },
              "on disproved message from {}", from
            )
          }
          log.log_cex(& from, & cex, & props) ;
          manager.broadcast( MsgDown::Forget(props, Status::Disproved) ) ;
        },

        Ok( Proved(props, from, info) ) => {
          log.log_proved(& from, & props, & info) ;
          let mut invs = STermSet::with_capacity(props.len()) ;
          for prop in props.iter() {
            match c.get_prop(prop) {
              None => {
                log.bad(
                  & Kino,
                  & format!("unknown property {} proved by {}", prop, from)
                ) ;
                continue
              },
              Some(ref prop) => {
                invs.insert( prop.0.body().clone() ) ;
                ()
              },
            }
            try_log_run!(
              c.set_prop_inv(prop, info.to_usize()), log, {
                result = Err(()) ;
                break 'msg_loop
              },
              "on proved message from {}", from
            )
          } ;
          manager.broadcast( MsgDown::Forget(props, Status::Proved) ) ;
          manager.broadcast( MsgDown::Invariants(sys.sym().clone(), invs) ) ;
        },

        Ok( KTrue(from, props, _, o) ) => {
          for prop in props.iter() {
            try_log_run!(
              c.set_prop_k_true( prop, o.to_usize() ), log, {
                result = Err(()) ;
                break 'msg_loop
              },
              "on proved message from {}", from
            )
          }
          manager.broadcast(
            MsgDown::KTrue(props, o)
          )
        },

        Ok( Invariants(from, sym, set, at) ) => {
          let prune_msg_sent = manager.prune_if_possible(
            from, sym.clone(), set.clone(), at,
            |blah| log.bad(& Kino, blah)
          ) ;
          if ! prune_msg_sent {
            // No pruner running, broadcasting as invariants.
            log.log(
              & from,
              & format!(
                "{} invariant{} discovered{}",
                set.len(),
                if set.len() == 1 { "" } else { "s" },
                if let Some(at) = at {
                  format!(" at {}", at)
                } else { format!("") }
              )
            ) ;
            try_log!(
              c.add_invs(& sym, set.clone()), log,
              "while adding {} invariants for {} from {} to context",
              set.len(), sym, from
            ) ;
            manager.broadcast(
              MsgDown::Invariants( sym, set )
            )
          }
        },

        Ok( PrunedInvariants(pruner, from, sym, set, old_card, at) ) => {
          let mut blah = format!(
            "{} invariant{} discovered{}",
            set.len(),
            if set.len() == 1 { "" } else { "s" },
            if let Some(at) = at {
              format!(" at {}", at)
            } else { format!("") }
          ) ;
          if set.len() != old_card {
            blah = format!(
              "{} ({} before pruning by {})", blah, old_card, pruner
            )
          } else {
            blah = format!(
              "{} (none were pruned away)", blah
            )
          }
          // blah = format!("{}:", blah) ;
          // for inv in set.iter() {
          //   blah = format!("{}\n  {}", blah, inv)
          // }
          log.log(
            & from,
            & blah
            // & format!(
            //   "{} invariant{} discovered",
            //   set.len(),
            //   if set.len() == 1 { "" } else { "s" }
            // )
          ) ;
          try_log!(
            c.add_invs( & sym, set.clone() ), log,
            "while adding {} invariants for {} from {} to context",
            set.len(), sym, from
          ) ;
          manager.broadcast(
            MsgDown::Invariants( sym, set )
          )
        },

        Ok( Done(from, Info::At(k)) ) => {
          log.log( & from, & format!("done at {}", k) ) ;
          try_log!(
            manager.forget(& from), log,
            "after reception of a `Done` at {} message from {}", k, from
          )
        },

        Ok( Done(from, info) ) => {
          log.log(& from, & format!("done {}", info)) ;
          try_log!(
            manager.forget(& from), log,
            "after reception of a `Done` message from {}", from
          )
        },

        Ok( msg ) => log.bad( & Kino, & format!("unknown message {}", msg) ),

        Err(e) => log.bad(
          & Kino, & format!("{:?}", e)
        )

      }
    }

    let some_prop_disproved = try_log_run!(
      c.some_prop_disproved(& props), log, {
        log.just_log_unknown() ;
        return Err(())
      }, "during post-run analysis"
    ) ;
    let some_prop_unknown = try_log_run!(
      c.some_prop_unknown(& props), log, {
        log.just_log_unknown() ;
        return Err(())
      }, "during post-run analysis"
    ) ;

    if ! some_prop_disproved {
      if ! some_prop_unknown {
        log.log_safe()
      } else {
        log.log_unknown(
          try_log_run!(
            c.unknown_props(& props), log, {
              log.just_log_unknown() ;
              return Err(())
            }, "during post-run analysis"
          ).into_iter()
        )
      }
    } else {
      log.log_unsafe()
    }

    log.trail() ;

    result

  }
}