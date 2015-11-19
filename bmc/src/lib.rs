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
extern crate event ;
extern crate unroll ;

use term::Offset2 ;
use term::smt::* ;
use term::smt::sync::* ;

use event::msg::{ Event, MsgDown, Info } ;

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
impl event::CanRun for Bmc {
  fn id(& self) -> event::Technique { event::Technique::Bmc }

  fn run(
    & self, sys: Sys, props: Vec<Prop>, mut event: Event
  ) {
    // event.log(
    //   & format!("checking {} propertie(s) on system {}", props.len(), sys.sym())
    // ) ;

    // event.log("creating solver") ;

    let conf = SolverConf::z3().print_success() ;
    let factory = event.factory().clone() ;
    let mut actlit = Actlit::mk(factory.clone()) ;

    let mut k = Offset2::init() ;

    match Solver::mk(z3_cmd(), conf, factory.clone()) {
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

          // event.log(& format!("check-sat assuming {}", lit)) ;

          let mut actlits = props.actlits() ;
          actlits.push(lit) ;

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
                & format!("could not perform check-sat\n{:?}", e)
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
            None => return (),
            Some(msgs) => for msg in msgs {
              match msg {
                MsgDown::Forget(ps) => try_error!(
                  props.forget(& mut solver, & ps),
                  event
                ),
                MsgDown::Invariants(_,_) => event.log(
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
                event.k_true(props.not_inhibited(), k.curr())
              },
              Err(e) => {
                event.error(
                  & format!("could not perform check-sat\n{:?}", e)
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
}


/** Configuration for BMC. */
#[derive(Clone)]
pub struct BmcConf {
  max: Option<usize>,
  solver: term::smt::SolverStyle,
}

impl BmcConf {
  /** Creates a default bmc configuration.
  Default is no max `k`, use z3. */
  #[inline(always)]
  pub fn default() -> Self {
    BmcConf {
      max: None, solver: term::smt::SolverStyle::Z3
    }
  }

  /** Sets the max `k`. */
  #[inline(always)]
  pub fn set_max(& mut self, k: usize) {
    self.max = Some(k)
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
  /** The solver style. */
  #[inline(always)]
  pub fn solver(& self) -> & term::smt::SolverStyle {
    & self.solver
  }
}
