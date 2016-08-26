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
#[macro_use]
extern crate common ;
extern crate unroll ;

use std::sync::Arc ;
use std::time::Duration ;
use std::thread::sleep ;

use term::Offset2 ;

use common::conf ;
use common::SolverTrait ;
use common::msg::{ Info, Event, MsgDown } ;

use system::{ Sys, Prop } ;

use unroll::* ;

macro_rules! try_error {
  ($e:expr, $event:expr, $($blah:expr),+) => (
    match $e {
      Ok(v) => v,
      Err(e) => {
        let blah = format!( $( $blah ),+ ) ;
        $event.error( & format!("{}\n{:?}", blah, e) ) ;
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

    mk_solver_run!(
      solver_conf, conf.smt_log(), "bmc", event.factory(),
      solver => kind(solver, sys, props, & mut event),
      msg => event.error(msg)
    )
  }
}

fn kind<
  'a,
  S: SolverTrait<'a>
>(
  mut solver: S, sys: Sys, props: Vec<Prop>, event: & mut Event
) {

  let mut actlit_factory = ActlitFactory::mk() ;

  // Reversed to unroll backwards.
  let check_offset = Offset2::init().rev() ;
  let mut k = check_offset.clone() ;

  // event.log("creating manager, declaring actlits") ;
  let mut props = try_error!(
    PropManager::mk(props, & mut solver, & sys),
    event,
    "while creating property manager"
  ) ;

  // event.log("declaring functions, init and trans") ;
  try_error!(
    sys.defclare_funs(& mut solver), event,
    "while declaring UFs, init and trans"
  ) ;

  // event.log("declare svar@0") ;
  try_error!(
    sys.declare_svars(& mut solver, check_offset.next()), event,
    // Unrolling backwards ~~~~~~~~~~~~~~~~~~~~~~^^^^
    "while declaring state variables"
  ) ;

  // event.log( & format!("unroll {}", k) ) ;
  try_error!(
    sys.unroll(& mut solver, & k), event,
    "while unrolling system"
  ) ;

  'out: loop {

    props.reset_inhibited() ;

    // event.log( & format!("activating state at {}", k) ) ;
    try_error!(
      props.activate_state(& mut solver, & k), event,
      "while activating one-state property"
    ) ;

    match event.recv() {
      None => return (),
      Some(msgs) => for msg in msgs {
        match msg {
          MsgDown::Forget(ps) => try_error!(
            props.forget(& mut solver, & ps), event,
            "while forgetting some properties\n\
            because of a `Forget` message (1)"
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
        // Unique, fresh actlit.
        let actlit = actlit_factory.mk_fresh() ;

        actlit.declare(& mut solver).expect(
          & format!(
            "while declaring activation literal in BMC at {}", k
          )
        ) ;

        // event.log(
        //   & format!(
        //     "defining actlit {}\nto imply {} at {}",
        //     lit, one_prop_false, check_offset
        //   )
        // ) ;
        let implication = actlit.activate_term(one_prop_false) ;

        try_error!(
          solver.assert(& implication, & k), event,
          "while asserting property falsification"
        ) ;

        // event.log(& format!("check-sat assuming {}", lit)) ;

        let mut actlits = props.actlits() ;
        // let prop_count = actlits.len() ;
        actlits.push(actlit.name()) ;

        // event.log(
        //   & format!(
        //     "checking {} properties @{} ({} unrolling(s))",
        //     props.len(),
        //     check_offset.next(),
        //     k.curr()
        //   )
        // ) ;

        match solver.check_sat_assuming( & actlits, & () ) {
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
                  props.forget(& mut solver, & unfalsifiable), event,
                  "while forgetting some properties\n\
                  because I just proved them invariant"
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
                          props.forget(& mut solver, & ps), event,
                          "while forgetting some properties\n\
                          because of a `Forget` message (2)"
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
                sleep(Duration::from_millis(10)) ;
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
    try_error!(
      sys.unroll(& mut solver, & k), event,
      "while unrolling system"
    ) ;

    // event.log( & format!("activate next at {}", k) ) ;
    try_error!(
      props.activate_next(& mut solver, & k), event,
      "while activating two state properties"
    ) ;

    ()

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


