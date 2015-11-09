// Copyright 2015 Adrien Champion. See the COPYRIGHT file at the top-level
// directory of this distribution.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

extern crate term ;
extern crate event ;
extern crate system ;
extern crate unroll ;

use std::thread::sleep_ms ;

use term::Offset2 ;
use term::smt::* ;
use term::smt::sync::* ;

use event::Event ;

use system::{ Sys, Prop } ;

use unroll::* ;

macro_rules! try_error {
  ($e:expr, $event:expr) => (
    match $e {
      Ok(v) => v,
      Err(e) => {
        $event.log( & format!("error: {:?}", e) ) ;
        panic!("error in bmc")
      },
    }
  )
}

pub fn run(
  sys: Sys, props: Vec<Prop>, event: Event
) {
  event.log(
    & format!("checking {} propertie(s) on system {}", props.len(), sys.sym())
  ) ;

  event.log("creating solver") ;

  let conf = SolverConf::z3().print_success() ;
  let factory = event.factory().clone() ;
  let mut actlit = Actlit::mk(factory.clone()) ;

  let mut k = Offset2::init() ;

  match Solver::mk(z3_cmd(), conf, factory.clone()) {
    Err(e) => event.log( & format!("error:\n  {:?}", e) ),
    Ok(mut solver) => {

      event.log("declaring functions, init and trans") ;
      try_error!(
        sys.defclare_funs(& mut solver), event
      ) ;

      event.log("declare svar@0 and assert init@0") ;
      try_error!(
        sys.assert_init(& mut solver, & k), event
      ) ;

      event.log("creating manager, declaring actlits") ;
      let props = try_error!(
        PropManager::mk(factory.clone(), props, & mut solver),
        event
      ) ;


      loop {

        let one_prop_false = props.one_false() ;

        let lit = actlit.mk_fresh_declare(& mut solver).unwrap() ;
        event.log(
          & format!(
            "defining actlit {}\nto imply {} at {}",
            lit, one_prop_false, k.curr()
          )
        ) ;
        let check = actlit.mk_impl(& lit, one_prop_false) ;

        try_error!(
          solver.assert(& check, & k), event
        ) ;

        event.log(
          & format!("check-sat assuming {}", lit)
        ) ;

        let mut actlits = props.actlits() ;
        actlits.push(lit) ;

        match solver.check_sat_assuming( & actlits, k.curr() ) {
          Ok(true) => {
            event.log("sat")
          },
          Ok(false) => {
            event.log("unsat")
          },
          Err(e) => event.log( & format!("{:?}", e) ),
        } ;

        event.log( & format!("unrolling to {}", k.next()) ) ;
        try_error!( sys.unroll(& mut solver, & k), event ) ;

        k = k.nxt() ;

        sleep_ms(500) ;

        ()

      }
    },
  }
}