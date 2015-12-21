#![deny(missing_docs)]
// Copyright 2015 Adrien Champion. See the COPYRIGHT file at the top-level
// directory of this distribution.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

/*! K-induction.

Unrolls backwards.
*/

extern crate term ;
extern crate system ;
extern crate common ;
extern crate unroll ;

use std::sync::Arc ;
use std::thread::sleep_ms ;

use term::Offset2 ;
use term::smt::* ;

use common::conf ;
use common::msg::{ Info, Event, MsgDown} ;

use system::{ Sys, Prop } ;

use unroll::* ;

macro_rules! try_error {
  ($e:expr, $event:expr) => (
    match $e {
      Ok(v) => v,
      Err(e) => {
        $event.error( & format!("{:?}", e) ) ;
        $event.done(Info::Error) ;
        return ()
      },
    }
  )
}

/** K-induction. */
pub struct KInd ;
unsafe impl Send for KInd {}
impl common::CanRun<conf::Kind> for KInd {
  fn id(& self) -> common::Tek { common::Tek::KInd }

  fn run(
    & self, conf: Arc<conf::Kind>, sys: Sys, props: Vec<Prop>, mut event: Event
  ) {
    // event.log(
    //   & format!("checking {} propertie(s) on system {}", props.len(), sys.sym())
    // ) ;

    // event.log("creating solver") ;

    let mut solver_conf = conf.smt().clone().default().print_success() ;
    match * conf.smt_cmd() {
      None => (),
      Some(ref cmd) => solver_conf = solver_conf.cmd(cmd.clone()),
    } ;

    let mut kid = match Kid::mk(solver_conf) {
      Ok(kid) => kid,
      Err(e) => {
        event.error( & format!("could not spawn solver kid\n{:?}", e) ) ;
        return ()
      },
    } ;

    kind(& mut kid, sys, props, & mut event, conf.smt_log()) ;
  }
}

fn kind(
  kid: & mut Kid, sys: Sys, props: Vec<Prop>,
  event: & mut Event, _smt_log: & Option<String>
) {
  match * _smt_log {
    None => (),
    Some(_) => event.warning("smt_log is not implemented")
  } ;

  let factory = event.factory().clone() ;
  let mut actlit = Actlit::mk(factory.clone()) ;

  // Reversed to unroll backwards.
  let check_offset = Offset2::init().rev() ;
  let mut k = check_offset.clone() ;

  match solver(kid, factory.clone()) {
    Err(e) => event.error( & format!("could not create solver\n{:?}", e) ),
    Ok(mut solver) => {

      // event.log("creating manager, declaring actlits") ;
      let mut props = try_error!(
        PropManager::mk(factory.clone(), props, & mut solver, & sys),
        event
      ) ;

      // event.log("declaring functions, init and trans") ;
      try_error!(
        sys.defclare_funs(& mut solver), event
      ) ;

      // event.log("declare svar@0") ;
      try_error!(
        sys.declare_svars(& mut solver, check_offset.next()), event
        // Unrolling backwards ~~~~~~~~~~~~~~~~~~~~~~^^^^
      ) ;

      // event.log( & format!("unroll {}", k) ) ;
      try_error!( sys.unroll(& mut solver, & k), event ) ;

      'out: loop {

        props.reset_inhibited() ;

        // event.log( & format!("activating state at {}", k) ) ;
        try_error!(
          props.activate_state(& mut solver, & k), event
        ) ;

        match event.recv() {
          None => return (),
          Some(msgs) => for msg in msgs {
            match msg {
              MsgDown::Forget(ps) => try_error!(
                props.forget(& mut solver, & ps),
                event
              ),
              MsgDown::Invariants(_,_) => event.warning(
                "received invariants, skipping"
              ),
              _ => event.error("unknown message")
            }
          },
        } ;

        if props.none_left() {
          event.done_at(& k.curr()) ;
          break
        }

        'split: loop {

            if let Some(one_prop_false) = props.one_false_next() {

            let lit = actlit.mk_fresh_declare(& mut solver).unwrap() ;
            // event.log(
            //   & format!(
            //     "defining actlit {}\nto imply {} at {}",
            //     lit, one_prop_false, check_offset
            //   )
            // ) ;
            let check = actlit.mk_impl(& lit, one_prop_false) ;

            try_error!(solver.assert(& check, & check_offset), event) ;

            // event.log(& format!("check-sat assuming {}", lit)) ;

            let mut actlits = props.actlits() ;
            // let prop_count = actlits.len() ;
            actlits.push(lit) ;

            // event.log(
            //   & format!(
            //     "checking {} properties @{} ({} unrolling(s))",
            //     props.len(),
            //     check_offset.next(),
            //     k.curr()
            //   )
            // ) ;

            match solver.check_sat_assuming( & actlits, check_offset.next() ) {
              Ok(true) => {
                // event.log("sat, getting falsified properties") ;
                match props.get_false_next(& mut solver, & check_offset) {
                  Ok(falsified) => {
                    // let mut s = "falsified:".to_string() ;
                    // for sym in falsified.iter() {
                    //   s = format!("{}\n  {}", s, sym)
                    // } ;
                    // event.log(& s) ;
                    props.inhibit(& falsified) ;
                  },
                  Err(e) => {
                    event.error(
                      & format!("could not get falsifieds\n{:?}", e)
                    ) ;
                    break
                  },
                }
              },
              Ok(false) => {
                // event.log("unsat") ;
                let unfalsifiable = props.not_inhibited() ;
                // Wait until we get something.
                loop {
                  let mut invariant = true ;
                  let at_least = k.curr().pre().unwrap() ;
                  for prop in unfalsifiable.iter() {
                    match * event.get_k_true(prop) {
                      Some(ref o) => {
                        if o < & at_least {
                          invariant = false ;
                          break
                        }
                      },
                      _ => { invariant = false ; break }
                    }
                  } ;
                  if invariant {
                    // event.log("forgetting") ;
                    try_error!(
                      props.forget(& mut solver, & unfalsifiable),
                      event
                    ) ;
                    event.proved_at(unfalsifiable, k.curr()) ; 
                    break 'split
                  } else {
                    // event.log("recv") ;
                    match event.recv() {
                      None => return (),
                      Some(msgs) => for msg in msgs {
                        match msg {
                          MsgDown::Forget(ps) => {
                            try_error!(
                              props.forget(& mut solver, & ps),
                              event
                            ) ;
                            continue 'out
                          },
                          MsgDown::Invariants(_,_) => event.log(
                            "received invariants, skipping"
                          ),
                          _ => event.error("unknown message")
                        }
                      },
                    } ;
                    sleep_ms(10) ;
                  }
                }
              },
              Err(e) => {
                event.error(
                  & format!("could not perform check-sat\n{:?}", e)
                ) ;
                break
              },
            } ;

            if props.all_inhibited() { break }
          } else {
            break 'split
          }
        } ;

        if props.none_left() {
          event.done_at( k.curr() ) ;
          break
        }

        k = k.nxt() ;

        // event.log( & format!("unroll {}", k) ) ;
        try_error!( sys.unroll(& mut solver, & k), event ) ;

        // event.log( & format!("activate next at {}", k) ) ;
        try_error!(
          props.activate_next(& mut solver, & k), event
        ) ;

        ()

      } ;
    },
  }
}


/** Configuration for k-induction. */
#[derive(Clone)]
pub struct KIndConf {
  max: Option<usize>,
  restart: bool,
  solver: term::smt::SolverStyle,
}

impl KIndConf {
  /** Creates a default k-induction configuration.
  Default is no max `k`, restart when max `k` reached, use z3. */
  #[inline(always)]
  pub fn default() -> Self {
    KIndConf {
      max: None, restart: true, solver: term::smt::SolverStyle::Z3
    }
  }

  /** Sets the max `k`. */
  #[inline(always)]
  pub fn set_max(& mut self, k: usize) {
    self.max = Some(k)
  }
  /** Sets the restart option. */
  #[inline(always)]
  pub fn set_restart(& mut self, b: bool) {
    self.restart = b
  }
  /** Sets the solver style. */
  #[inline(always)]
  pub fn set_solver(& mut self, s: term::smt::SolverStyle) {
    self.solver = s
  }

  /** The max `k`. */
  #[inline(always)]
  pub fn max(& self) -> & Option<usize> {
    & self.max
  }
  /** True if the solver should restart when max `k` is reached. */
  #[inline(always)]
  pub fn restart(& self) -> bool {
    self.restart
  }
  /** The solver style. */
  #[inline(always)]
  pub fn solver(& self) -> & term::smt::SolverStyle {
    & self.solver
  }
}


