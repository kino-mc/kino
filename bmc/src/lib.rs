// Copyright 2016 Adrien Champion. See the COPYRIGHT file at the top-level
// directory of this distribution.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.
#![deny(missing_docs)]

//! Bounded model-checking.


extern crate term ;
extern crate system ;
#[macro_use]
extern crate common ;
extern crate unroll ;

use std::sync::Arc ;

use term::Offset2 ;
use term::smt::SolverStyle ;

use common::{ SolverTrait, CanRun } ;
use common::conf ;
use common::msg::{ Event, MsgDown } ;

use system::{ Sys, Prop } ;

use unroll::* ;

/// Bounded model-checking.
pub struct Bmc ;
unsafe impl Send for Bmc {}
impl CanRun<conf::Bmc> for Bmc {
  fn id(& self) -> common::Tek { common::Tek::Bmc }

  fn run(
    & self, conf: Arc<conf::Bmc>, sys: Sys, props: Vec<Prop>, mut event: Event
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
      solver => bmc(solver, sys, props, & mut event),
      err => event.error(err)
    )
  }
}


fn bmc<
  'a, S: SolverTrait<'a>
>(
  solver: S, sys: Sys, props: Vec<Prop>, event: & mut Event
) {
  let init_off = Offset2::init() ;
  let mut k = Offset2::init() ;

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

  // event.log("declare svar@0 and assert init@0") ;
  log_try!(
    event, unroller.assert_init(& k)
    => "while asserting init"
  ) ;

  // event.log("asserting one-state invariants") ;
  log_try!(
    event, unroller.assert_os_invs(& k)
    => "while asserting one state invariants"
  ) ;

  props.reset_inhibited() ;

  // Check for init is separate since only one-state properties must be
  // checked.
  let mut doing_init = true ;

  'unroll: loop {

    if ! doing_init {
      log_try!(
        event, unroller.unroll(& k)
        => "while unrolling system at {}", k
      ) ;
    }

    props.reset_inhibited() ;

    match event.recv() {
      None => break,
      Some(msgs) => for msg in msgs {
        match msg {
          MsgDown::Forget(ps, _) => log_try!(
            event, props.forget(unroller.solver(), ps.iter())
            => "while forgetting property in manager"
          ),
          MsgDown::Invariants(sym, invs) => if sys.sym().get() == & sym  {
            // event.log(
            //   & format!("received {} invariants", invs.len())
            // ) ;
            log_try!(
              event, unroller.add_invs(invs, & init_off, & k)
              => "while adding invariants from supervisor"
            )
          },
          msg => event.error(
            format!("unexpected message `{:?}`", msg).into()
          )
        }
      },
    } ;

    if props.none_left() {
      event.done_at(k.curr()) ;
      break
    }

    // Check that the unrolling is satisfiable by itself.
    if ! log_try!(
      event, unroller.check_sat()
      => "could not perform `check-sat`"
    ) {
      // No more transitions can be taken, all remaining properties
      // hold.
      event.proved_at( props.not_inhibited(), k.curr() ) ;
      event.warning(
        & format!("no more reachable state after {} transitions", k)
      ) ;
      event.done_at(k.curr()) ;
      return ()
    } ;

    'this_k: loop {
      
      // If we're doing init, only check one state properties.
      if let Some(
        one_prop_false
      ) = if doing_init {
        props.one_false_state()
      } else { props.one_false_next() } {

        // Setting up the negative actlit.
        let actlit = log_try!(
          event, unroller.fresh_actlit()
          => "while declaring activation literal at {}", k
        ) ;
        let implication = actlit.activate_term(one_prop_false) ;

        log_try!(
          event, unroller.assert(& implication, & k)
          => "while asserting implication at {} (2)", k
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
          // event.log("sat, getting falsified properties") ;
          let falsified = log_try!(
            event, if doing_init {
              props.get_false_state(unroller.solver(), & k)
            } else {
              props.get_false_next(unroller.solver(), & k)
            } => "could not retrieve falsified properties"
          ) ;
          let model = log_try!(
            event, unroller.solver().get_model()
            => "could not retrieve model"
          ) ;
          log_try!(
            event, props.forget(unroller.solver(), falsified.iter())
            => "while forgetting property in manager"
          ) ;
          log_try!(
            event, unroller.deactivate(actlit)
            => "could not deactivate negative actlit"
          ) ;
          event.disproved_at(model, falsified, k.curr())
        } else {
          // event.log("unsat") ;
          event.k_true(props.not_inhibited(), k.curr()) ;
          log_try!(
            event, unroller.deactivate(actlit)
            => "could not deactivate negative actlit"
          ) ;
          break 'this_k
        }

      } else {
        if props.none_left() {
          // No more properties to check, done.
          event.log( & format!("no property left at {}", k) ) ;
          event.done_at(k.curr()) ;
          return ()
        } else {
          // Keep going.
          // Why? It seems at this point there's no property left. Well not
          // necessarily.
          //
          // If we're `doing_init` we're only checking for one-state
          // properties. There might be none, but there might be two-state
          // properties left. In this case, we end up in this branch and we
          // must keep going to check them.
          break 'this_k
        }
      }

    }

    if ! doing_init {
      k = k.nxt()
    } else {
      doing_init = false
    }

  }
}

/// Configuration for BMC.
#[derive(Clone)]
pub struct BmcConf {
  /// Max number of unrolling.
  max: Opt< Option<usize> >,
  /// Solver to use.
  solver: Opt< SolverStyle >,
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