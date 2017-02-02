// Copyright 2016 Adrien Champion. See the COPYRIGHT file at the top-level
// directory of this distribution.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.
#![deny(missing_docs)]

//! Pruner.

#[macro_use]
extern crate error_chain ;
extern crate term ;
extern crate system ;
#[macro_use]
extern crate common ;
extern crate unroll ;

use std::sync::Arc ;
use std::time::Duration ;
use std::thread::sleep ;

use term::{ Offset2, STermSet } ;

use common::conf ;
use common::SolverTrait ;
use common::msg::{ Event, MsgDown } ;
use common::errors::* ;

use system::{ Sys, Prop } ;

use unroll::* ;

/// Pruner.
pub struct Pruner ;
unsafe impl Send for Pruner {}
impl common::CanRun<conf::Pruner> for Pruner {
  fn id(& self) -> common::Tek { common::Tek::Pruner }

  fn run(
    & self, conf: Arc<conf::Pruner>, sys: Sys,
    props: Vec<Prop>, mut event: Event
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
      solver_conf, conf.smt_log(), "pruner", event.factory(),
      solver => pruner(solver, sys, props, & mut event),
      err => event.error(err)
    )
  }
}

fn pruner< 'a, S: SolverTrait<'a> >(
  solver: S, sys: Sys, _: Vec<Prop>, event: & mut Event
) {

  let duration = Duration::from_millis(73) ;

  let init = Offset2::init() ;

  let mut unroller = log_try!(
    event, Unroller::mk(& sys, & [], solver)
    => "while creating unroller"
  ) ;

  log_try!(
    event, unroller.declare_svars(
      init.curr()
    ) => "while declaring state variables at {}", init.curr()
  ) ;

  log_try!(
    event, unroller.unroll_init(& init)
    => "while unrolling system at {}", init
  ) ;

  let mut to_do = None ;

  loop {
    match event.recv() {
      None => return (),
      Some(msgs) => for msg in msgs {
        match msg {
          MsgDown::Invariants(sym, invs) => if * sys == sym  {
            log_try!(
              event, unroller.add_invs(invs, & init, & init)
              => "while adding invariants from supervisor"
            )
          },
          MsgDown::InvariantPruning(tek, sym, invs, info) => if * sys == sym {
            to_do = Some( (tek, invs, info) )
          },
          _ => (),
        }
      },
    }
    match to_do {
      Some( (tek, invs, info) ) => {
        let old_len = invs.len() ;
        let invariants = log_try!(
          event, prune(& mut unroller, event, invs, & init)
        ) ;
        event.pruned_invariants(
          tek, sys.sym(), invariants, old_len, info
        )
      },
      None => sleep(duration),
    }
    to_do = None
  }
}


fn prune< 'a, S: SolverTrait<'a> >(
  unroller: & mut Unroller<S>, _event: & mut Event, invars: STermSet,
  k: & Offset2
) -> Res<STermSet> {

  let mut non_trivial_invs = STermSet::with_capacity( invars.len() ) ;

  let mut invs = try_chain!(
    InvManager::mk( invars, unroller.solver() )
    => "while creating invariant manager"
  ) ;

  'split: while let Some(one_inv_false) = invs.one_false_next() {
        
    // Setting up the negative actlit.
    let actlit = try_chain!(
      unroller.fresh_actlit()
      => "while declaring activation literal at {}", k
    ) ;
    let implication = actlit.activate_term(one_inv_false) ;

    try_chain!(
      unroller.assert(& implication, & k)
      => "while asserting property falsification"
    ) ;

    // Building list of actlits for this check.
    let mut actlits = invs.actlits() ;
    actlits.push(actlit.name()) ;

    // Check sat.
    let is_sat = try_chain!(
      unroller.check_sat_assuming( & actlits )
      => "during a `check_sat_assuming` query at {}", k
    ) ;

    if is_sat {
      // _event.log("sat, getting falsified invs") ;
      let falsified = try_chain!(
        invs.get_false_next(unroller.solver(), & k)
        => "could not retrieve falsified properties"
      ) ;
      // _event.log(
      //   & format!("{} falsified invs", falsified.len())
      // ) ;
      try_chain!(
        unroller.deactivate(actlit)
        => "while deactivating negative actlit"
      ) ;
      try_chain!(
        invs.forget(unroller.solver(), falsified.iter())
        => "while forgetting {} falsified properties", falsified.len()
      ) ;
      for falsified in falsified.into_iter() {
        non_trivial_invs.insert(falsified) ; ()
      }
    } else {
      // event.log("unsat") ;
      break
    }
  }

  return Ok( non_trivial_invs )
}



