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
extern crate event ;
extern crate system ;
extern crate unroll ;

use std::thread::sleep_ms ;

use term::Offset2 ;
use term::smt::* ;
use term::smt::sync::* ;

use event::{ Event, MsgDown, Info } ;

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
impl event::CanRun for KInd {
  fn id(& self) -> event::Technique { event::Technique::KInd }

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

    // Reversed to unroll backwards.
    let check_offset = Offset2::init().rev() ;
    let mut k = check_offset.clone() ;

    match Solver::mk(z3_cmd(), conf, factory.clone()) {
      Err(e) => event.error( & format!("could not create solver\n{:?}", e) ),
      Ok(mut solver) => {

        // event.log("creating manager, declaring actlits") ;
        let mut props = try_error!(
          PropManager::mk(factory.clone(), props, & mut solver),
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
                MsgDown::Invariants(_,_) => event.log(
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

            let one_prop_false = props.one_false_next() ;

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
            //     "checking {} properties @{}",
            //     props.len(),
            //     check_offset.next()
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
                    event.proved_at(unfalsifiable, k.next()) ; 
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
          } ;

          if props.none_left() {
            event.done_at(k.next()) ;
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
}


