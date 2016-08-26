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
#[macro_use]
extern crate common ;
extern crate unroll ;

use std::sync::Arc ;

use term::{ Term, Offset2, Factory } ;
use term::smt::* ;

use common::conf ;
use common::msg::{ Event, MsgDown, Info } ;

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

    let mut solver_conf = conf.smt().clone().default().print_success() ;
    match * conf.smt_cmd() {
      None => (),
      Some(ref cmd) => solver_conf = solver_conf.cmd(cmd.clone()),
    } ;

    mk_solver_run!(
      solver_conf, conf.smt_log(), "bmc", event.factory(),
      solver => bmc(solver, sys, props, & mut event),
      msg => event.error(msg)
    )
  }
}


fn bmc<
  'a,
  S: Solver<'a, Factory>
      + Query<'a, Factory>
      + QueryIdent<'a, Factory, (), String>
      + QueryExprInfo<'a, Factory, Term>
>(
  mut solver: S, sys: Sys, props: Vec<Prop>, event: & mut Event
) {
  let mut k = Offset2::init() ;

  let mut actlit_factory = ActlitFactory::mk() ;

  // event.log("creating manager, declaring actlits") ;
  let mut props = try_error!(
    PropManager::mk(props, & mut solver, & sys),
    event,
    "while creating property manager"
  ) ;

  if props.none_left() {
    event.done_at(k.curr()) ;
    return ()
  }

  // event.log("declaring functions, init and trans") ;
  try_error!(
    sys.defclare_funs(& mut solver), event,
    "while declaring UFs, init and trans"
  ) ;

  // event.log("declare svar@0 and assert init@0") ;
  try_error!(
    sys.assert_init(& mut solver, & k), event,
    "while asserting init"
  ) ;

  props.reset_inhibited() ;

  // Check for init is separate since only one-state properties must be
  // checked.
  let mut doing_init = false ;

  'unroll: loop {

    if ! doing_init {
      try_error!(
        sys.unroll(& mut solver, & k), event,
        "while unrolling system at {}", k
      ) ;
    }

    props.reset_inhibited() ;

    match event.recv() {
      None => break,
      Some(msgs) => for msg in msgs {
        match msg {
          MsgDown::Forget(ps, _) => try_error!(
            props.forget(& mut solver, ps.iter()),
            event,
            "while forgetting property in manager"
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

    // Check that the unrolling is satisfiable by itself.
    if ! try_error!(
      solver.check_sat(), event,
      "could not perform `check-sat`"
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
        let actlit = actlit_factory.mk_fresh() ;
        actlit.declare(& mut solver).expect(
          & format!(
            "while declaring activation literal at {}", k
          )
        ) ;
        let implication = actlit.activate_term(one_prop_false) ;

        try_error!(
          solver.assert(& implication, & k), event,
          "while asserting implication at {} (2)", k
        ) ;

        // Building list of actlits for this check.
        let mut actlits = props.actlits() ;
        actlits.push(actlit.name()) ;

        // Check sat.
        let is_sat = try_error!(
          solver.check_sat_assuming( & actlits, & () ), event,
          "during a `check_sat_assuming` query at {}", k
        ) ;

        if is_sat {
          // event.log("sat, getting falsified properties") ;
          let falsified = try_error!(
            props.get_false_next(& mut solver, & k), event,
            "could not retrieve falsified properties"
          ) ;
          let model = try_error!(
            solver.get_model(), event,
            "could not retrieve model"
          ) ;
          try_error!(
            props.forget(& mut solver, falsified.iter()), event,
            "while forgetting property in manager"
          ) ;
          try_error!(
            actlit.deactivate(& mut solver), event,
            "could not deactivate negative actlit"
          ) ;
          event.disproved_at(model, falsified, k.curr())
        } else {
          // event.log("unsat") ;
          event.k_true(props.not_inhibited(), k.curr()) ;
          try_error!(
            actlit.deactivate(& mut solver), event,
            "could not deactivate negative actlit"
          ) ;
          break 'this_k
        }

      } else {
        // No more properties to check, done.
        event.log( & format!("no property left at {}", k) ) ;
        event.done_at(k.curr()) ;
      }

    }

    k = k.nxt() ;

    doing_init = false
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