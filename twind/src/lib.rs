// Copyright 2015 Adrien Champion. See the COPYRIGHT file at the top-level
// directory of this distribution.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.
#![deny(missing_docs)]

//! 2-induction.
//!
//! Unrolls backwards.

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
use common::msg::{ Event, MsgDown, Status } ;

use system::{ Sys, Prop } ;

use unroll::* ;

/// K-induction.
pub struct Twind ;
unsafe impl Send for Twind {}
impl common::CanRun<conf::Twind> for Twind {
  fn id(& self) -> common::Tek { common::Tek::Twind }

  fn run(
    & self, conf: Arc<conf::Twind>, sys: Sys, props: Vec<Prop>,
    mut event: Event
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
      solver_conf, conf.smt_log(), "twind", event.factory(),
      solver => twind(solver, sys, props, & mut event),
      err => event.error(err)
    )
  }
}

fn twind<
  'a,
  S: SolverTrait<'a>
>(
  solver: S, sys: Sys, props: Vec<Prop>, event: & mut Event
) {

  let duration = Duration::from_millis(73) ;

  // Reversed to unroll backwards.
  let check_offset = Offset2::init().rev() ;
  let k = check_offset.clone() ;

  let mut unroller = log_try!(
    event, Unroller::mk(& sys, & props, solver)
    => "while creating unroller"
  ) ;

  // event.log("creating manager, declaring actlits") ;
  let mut props = log_try!(
    event, PropManager::mk(props, unroller.solver())
    => "while creating property manager"
  ) ;

  if props.none_left() {
    event.log("no properties to run on, stopping") ;
    event.done_at(k.curr()) ;
    return ()
  }

  // event.log("declaring functions, init and trans") ;
  // try_error!(
  //   unroller.defclare_funs(), event,
  //   "while declaring UFs, init and trans"
  // ) ;

  // event.log("declare svar@0") ;
  log_try!(
    event, unroller.declare_svars(check_offset.next())
    // Unrolling backwards ~~~~~~~~~~~~~^^^^
    => "while declaring state variables"
  ) ;

  // event.log( & format!("unroll {}", k) ) ;
  log_try!(
    event, unroller.unroll_init(& k)
    => "while unrolling system at {}", k
  ) ;
  log_try!(
    event, props.activate_state(unroller.solver(), & k)
    => "while activating one state properties"
  ) ;

  let k = k.nxt() ;

  log_try!(
    event, unroller.unroll_bak(& k)
    => "while unrolling system at {}", k
  ) ;

  log_try!(
    event, props.activate_next(unroller.solver(), & k)
    => "while activating two state properties"
  ) ;
  log_try!(
    event, props.activate_state(unroller.solver(), & k)
    => "while activating one state properties"
  ) ;

  'out: loop {

    props.reset_inhibited() ;

    // event.log( & format!("activating state at {}", k) ) ;
    log_try!(
      event, props.activate_state(unroller.solver(), & k)
      => "while activating one-state property"
    ) ;

    match event.recv() {
      None => return (),
      Some(msgs) => for msg in msgs {
        match msg {
          MsgDown::Forget(ps, _) => log_try!(
            event, props.forget(unroller.solver(), ps.iter())
            => "while forgetting some properties\n\
              because of a `Forget` message (1)"
          ),
          MsgDown::Invariants(sym, invs) => if sys.sym().get() == & sym  {
            log_try!(
              event, unroller.add_invs(invs, & check_offset, & k)
              => "while adding invariants from supervisor"
            )
          },
          msg => event.error(
            format!("unexpected message `{:?}`", msg).into()
          ),
        }
      },
    }

    if props.none_left() {
      event.done_at(& k.curr()) ;
      break 'out
    }

    // event.log("splitting") ;

    'split: while let Some(one_prop_false) = props.one_false_next() {
        
      // Setting up the negative actlit.
      let actlit = log_try!(
        event, unroller.fresh_actlit()
        => "while declaring activation literal at {}", k
      ) ;
      let implication = actlit.activate_term(one_prop_false) ;

      log_try!(
        event, unroller.assert(& implication, & check_offset)
        => "while asserting property falsification"
      ) ;

      // Building list of actlits for this check.
      let mut actlits = props.actlits() ;
      actlits.push(actlit.name()) ;

      // Check sat.
      let is_sat = log_try!(
        event, unroller.check_sat_assuming( & actlits )
        => "during a `check_sat_assuming` query at {}", k
      ) ;

      if is_sat {
        // event.log("sat, getting falsified props") ;
        let falsified = log_try!(
          event, props.get_false_next(unroller.solver(), & check_offset)
          => "could not retrieve falsified properties"
        ) ;
        log_try!(
          event, unroller.deactivate(actlit)
          => "while deactivating negative actlit"
        ) ;
        log_try!(
          event, props.inhibit(& falsified)
          => "while inhibiting {} falsified properties", falsified.len()
        )
      } else {
        // event.log("unsat") ;
        log_try!(
          event, unroller.deactivate(actlit)
          => "while deactivating negative actlit"
        ) ;
        let mut unfalsifiable = props.not_inhibited_set() ;

        // Wait until we get something from BMC.
        // event.log("waiting for bmc") ;
        loop {
          let mut invariant = true ;
          let at_least = k.curr().pre() ;
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
            log_try!(
              event, props.forget(
                unroller.solver(), unfalsifiable.iter()
              )
              => "while forgetting some properties \
                because I just proved them invariant"
            ) ;
            event.proved_at(unfalsifiable.into_iter().collect(), k.curr()) ; 
            break 'split
          } else {
            // event.log("recv") ;
            match event.recv() {
              None => return (),
              Some(msgs) => {
                let mut disproved = false ;
                for msg in msgs {
                  match msg {
                    MsgDown::Forget(ps, Status::Proved) => {
                      log_try!(
                        event, props.forget(unroller.solver(), ps.iter())
                        => "while forgetting some properties \
                          because of a `Forget` message (2, proved)"
                      ) ;
                      for p in ps.iter() {
                        let _ = unfalsifiable.remove(p) ;
                        ()
                      }
                    },
                    MsgDown::Forget(ps, Status::Disproved) => {
                      log_try!(
                        event, props.forget(unroller.solver(), ps.iter())
                        => "while forgetting some properties \
                          because of a `Forget` message (2, disproved)"
                      ) ;
                      for p in ps.iter() {
                        disproved = disproved || unfalsifiable.remove(p)
                      }
                    },
                    MsgDown::Invariants(sym, invs) =>
                    if sys.sym().get() == & sym  {
                      // event.log(
                      //   & format!("received {} invariants", invs.len())
                      // ) ;
                      // event.log(
                      //   & format!("add_invs [{}, {}]", check_offset, k)
                      // ) ;
                      log_try!(
                        event, unroller.add_invs(invs, & check_offset, & k)
                        => "while adding invariants from supervisor"
                      )
                    },
                    msg => event.error(
                      format!("unexpected message `{:?}`", msg).into()
                    ),
                  }
                }

                if disproved {
                  // One of the unfalsifiable properties was falsified.
                  // Need to restart the check.
                  continue 'split
                }
              },
            } ;
            if props.none_left() {
              event.done_at( k.curr() ) ;
              break 'out
            }
            sleep(duration)
          }
        }
      }

      match event.recv() {
        None => return (),
        Some(msgs) => for msg in msgs {
          match msg {
            MsgDown::Forget(ps, _) => log_try!(
              event, props.forget(unroller.solver(), ps.iter())
              => "while forgetting some properties \
                because of a `Forget` message (1)"
            ),
            MsgDown::Invariants(sym, invs) => if sys.sym().get() == & sym  {
              // event.log(
              //   & format!("received {} invariants", invs.len())
              // ) ;
              // event.log( & format!("add_invs [{}, {}]", check_offset, k) ) ;
              log_try!(
                event, unroller.add_invs(invs, & check_offset, & k)
                => "while adding invariants from supervisor"
              )
            },
            msg => event.error(
              format!("unexpected message `{:?}`", msg).into()
            ),
          }
        },
      }

    }

    // event.log("checking if there's some properties left") ;
    if props.none_left() {
      event.done_at( k.curr() ) ;
      break
    }

    let mut new_stuff = false ;

    'new_stuff: while ! new_stuff {

      match event.recv() {
        None => return (),
        Some(msgs) => for msg in msgs {
          match msg {
            MsgDown::Forget(ps, _) => {
              new_stuff = true ;
              log_try!(
                event, props.forget(unroller.solver(), ps.iter())
                => "while forgetting some properties\n\
                  because of a `Forget` message (1)"
              )
            },
            MsgDown::Invariants(sym, invs) => if sys.sym().get() == & sym  {
              new_stuff = true ;
              // event.log(
              //   & format!("received {} invariants", invs.len())
              // ) ;
              // event.log( & format!("add_invs [{}, {}]", check_offset, k) ) ;
              log_try!(
                event, unroller.add_invs(invs, & check_offset, & k)
                => "while adding invariants from supervisor"
              )
            },
            msg => event.error(
              format!("unexpected message `{:?}`", msg).into()
            ),
          }
        },
      }

      sleep(duration)
    }

  }
}



