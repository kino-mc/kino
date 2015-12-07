#![deny(missing_docs)]
// Copyright 2015 Adrien Champion. See the COPYRIGHT file at the top-level
// directory of this distribution.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

/*! Bounded model-checking.

# To do

* factor code for check of the initial state and the succeeding ones
* check that unrolling of the transition relation is sat

*/

extern crate term ;
extern crate system ;
extern crate common ;
extern crate unroll ;

use std::sync::Arc ;

use term::Offset2 ;
use term::smt::* ;

use common::conf ;
use common::msg::{ Event, MsgDown, Info } ;

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

/** Bounded model-checking. */
pub struct Bmc ;
unsafe impl Send for Bmc {}
impl common::CanRun<conf::Bmc> for Bmc {
  fn id(& self) -> common::Tek { common::Tek::Bmc }

  fn run(
    & self, conf: Arc<conf::Bmc>, sys: Sys, props: Vec<Prop>, mut event: Event
  ) {
    // event.log(
    //   & format!("checking {} propertie(s) on system {}", props.len(), sys.sym())
    // ) ;

    // event.log("creating solver") ;

    let mut solver_conf = conf.solver().clone().default().print_success() ;
    match * conf.solver_cmd() {
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

    bmc(& mut kid, sys, props, & mut event, conf.smt_log()) ;
  }
}


fn bmc(
  kid: & mut Kid, sys: Sys, props: Vec<Prop>,
  event: & mut Event, _smt_log: & Option<String>
) {
  // use std::fs::OpenOptions ;

  match * _smt_log {
    None => (),
    Some(_) => event.warning("smt_log is not implemented")
  } ;

  let factory = event.factory().clone() ;
  let mut actlit = Actlit::mk(factory.clone()) ;
  let mut k = Offset2::init() ;

  match solver(kid, factory.clone()) {
    Err(e) => event.error( & format!("could not create solver\n{:?}", e) ),
    Ok(mut solver) => {

      // event.log("declaring functions, init and trans") ;
      try_error!(
        sys.defclare_funs(& mut solver), event
      ) ;

      // event.log("declare svar@0 and assert init@0") ;
      try_error!(
        sys.assert_init(& mut solver, & k), event
      ) ;

      // event.log("creating manager, declaring actlits") ;
      let mut props = try_error!(
        PropManager::mk(factory.clone(), props, & mut solver),
        event
      ) ;


      // Check for init is separate since only one-state properties must be
      // checked.

      props.reset_inhibited() ;

      if props.none_left() {
        event.done_at(k.curr()) ;
        return ()
      }

      if let Some(one_prop_false) = props.one_false_state() {

        let lit = actlit.mk_fresh_declare(& mut solver).unwrap() ;
        // event.log(
        //   & format!(
        //     "defining actlit {}\nto imply {} at {}",
        //     lit, one_prop_false, k
        //   )
        // ) ;
        let check = actlit.mk_impl(& lit, one_prop_false) ;

        try_error!(solver.assert(& check, & k), event) ;

        let mut actlits = props.actlits() ;
        actlits.push(lit) ;

        match solver.check_sat() {
          Ok(true) => (),
          Ok(false) => {
            // No more transitions can be taken, all remaining properties
            // hold.
            event.proved_at( props.not_inhibited(), k.curr() ) ;
            event.warning("no more reachable state") ;
            event.done_at(k.curr()) ;
            return ()
          },
          Err(e) => {
            event.error(
              & format!("could not perform check-sat\n{:?}", e)
            ) ;
            return ()
          },
        } ;

        // event.log(
        //   & format!(
        //     "checking {} properties @{}",
        //     props.len(),
        //     k.curr()
        //   )
        // ) ;

        match solver.check_sat_assuming( & actlits, k.next() ) {
          Ok(true) => {
            // event.log("sat, getting falsified properties") ;
            match props.get_false_state(& mut solver, & k) {
              Ok(falsified) => {
                // let mut s = "falsified:".to_string() ;
                // for sym in falsified.iter() {
                //   s = format!("{}\n  {}", s, sym)
                // } ;
                // event.log(& s) ;

                match solver.get_model() {
                  Ok(model) => {
                    try_error!(
                      props.forget(& mut solver, & falsified), event
                    ) ;
                    event.disproved_at(model, falsified, k.curr())
                  },
                  Err(e) => {
                    event.error(
                      & format!("could not get model:\n{:?}", e)
                    ) ;
                    event.done(Info::Error) ;
                    return ()
                  },
                } ;
              },
              Err(e) => {
                event.error(
                  & format!("could not get falsifieds\n{:?}", e)
                ) ;
                return ()
              },
            }
          },
          Ok(false) => {
            event.k_true(props.not_inhibited(), k.curr())
          },
          Err(e) => {
            event.error(
              & format!("could not perform check-sat-assuming\n{:?}", e)
            ) ;
            return ()
          },
        } ;

        if props.none_left() {
          event.done_at(k.curr()) ;
          return ()
        }
      } ;

      try_error!( sys.unroll(& mut solver, & k), event ) ;

      k = k.nxt() ;


      loop {

        props.reset_inhibited() ;

        match event.recv() {
          None => break,
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
          event.done_at(k.curr()) ;
          break
        }

        // event.log( & format!("unrolling at {}", k) ) ;
        try_error!( sys.unroll(& mut solver, & k), event ) ;

        if let Some(one_prop_false) = props.one_false_next() {

          let lit = actlit.mk_fresh_declare(& mut solver).unwrap() ;
          // event.log(
          //   & format!(
          //     "defining actlit {}\nto imply {} at {}",
          //     lit, one_prop_false, k
          //   )
          // ) ;
          let check = actlit.mk_impl(& lit, one_prop_false) ;

          try_error!(solver.assert(& check, & k), event) ;

          // event.log(& format!("check-sat assuming {}", lit)) ;

          let mut actlits = props.actlits() ;
          actlits.push(lit) ;

          match solver.check_sat() {
            Ok(true) => (),
            Ok(false) => {
              // No more transitions can be taken, all remaining properties
              // hold.
              event.proved_at( props.not_inhibited(), k.next() ) ;
              event.warning("no more reachable state") ;
              event.done_at( k.next() ) ;
              break
            },
            Err(e) => {
              event.error(
                & format!("could not perform check-sat\n{:?}", e)
              ) ;
              break
            },
          } ;

          // event.log(
          //   & format!(
          //     "checking {} properties @{}",
          //     props.len(),
          //     k.curr()
          //   )
          // ) ;

          match solver.check_sat_assuming( & actlits, k.next() ) {
            Ok(true) => {
              // event.log("sat, getting falsified properties") ;
              match props.get_false_next(& mut solver, & k) {
                Ok(falsified) => {
                  // let mut s = "falsified:".to_string() ;
                  // for sym in falsified.iter() {
                  //   s = format!("{}\n  {}", s, sym)
                  // } ;
                  // event.log(& s) ;

                  // event.log("getting model") ;
                  match solver.get_model() {
                    Ok(model) => {
                      // event.log("got model") ;
                      try_error!(
                        props.forget(& mut solver, & falsified), event
                      ) ;
                      // event.log("communicating model") ;
                      event.disproved_at(model, falsified, k.curr())
                    },
                    Err(e) => {
                      event.error(
                        & format!("could not get model:\n{:?}", e)
                      ) ;
                      event.done(Info::Error) ;
                      break
                    },
                  } ;
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
              event.k_true(props.not_inhibited(), k.curr())
            },
            Err(e) => {
              event.error(
                & format!("could not perform check-sat-assuming\n{:?}", e)
              ) ;
              break
            },
          } ;

          if props.none_left() {
            event.done_at(k.curr()) ;
            break
          }
        }

        k = k.nxt()

      } ;
    },
  }
}

/// Configuration for BMC.
#[derive(Clone)]
pub struct BmcConf {
  /// Max number of unrolling.
  max: Opt< Option<usize> >,
  /// Solver to use.
  solver: Opt< term::smt::SolverStyle >,
  /// Optional file path to log the smt trace to.
  smt_trace: Opt< Option<String> >,
}

impl BmcConf {
  /** Creates a default bmc configuration.
  Default is no max `k`, use z3, no smt trace. */
  #[inline(always)]
  pub fn default() -> Self {
    // Building the list of acceptable solver styles.
    let keys = SolverStyle::str_keys() ;
    let mut keys = keys.iter() ;
    let keys = if let Some(key) = keys.next() {
      keys.fold(
        key.to_string(),
        |s, key| format!("{}|{}", s, key)
      )
    } else { "".to_string() } ;

    // Building the actual conf.
    BmcConf {
      max: Opt::mk(
        ("max", ": <int> (none)".to_string()),
        vec![
          "Maximum number of unrollings in BMC.".to_string(),
        ],
        None
      ),
      solver: Opt::mk(
        ("solver", format!(": {} (z3)", keys)),
        vec![
          "Kind of solver BMC should use.".to_string(),

        ],
        term::smt::SolverStyle::Z3
      ),
      smt_trace: Opt::mk(
        ("smt_trace", ": <file> (none)".to_string()),
        vec![
          "File the SMT trace should be logged to.".to_string(),
        ],
        None
      ),
    }
  }

  /// Description of the BMC options.
  pub fn desc(& self) -> String {
    let mut s = "|===| Bounded model checking (BMC) options.\n".to_string() ;
    let pref = "| " ;
    self.max.append(& mut s, pref) ;
    s.push('\n') ;
    self.solver.append(& mut s, pref) ;
    s.push('\n') ;
    self.smt_trace.append(& mut s, pref) ;
    s.push_str("\n|===|") ;
    s
  }
}