extern crate term ;
extern crate event ;
extern crate system ;

use term::Offset2 ;
use term::smt::* ;

use event::Event ;

use system::{ CallSet, Callable, Sys, Prop } ;
use system::smt::Unroller ;

macro_rules! try_error {
  ($e:expr, $event:expr) => (
    match $e {
      Ok(()) => (),
      Err(e) => $event.log( & format!("error: {:?}", e) ),
    }
  )
}

pub fn run(
  sys: Sys, props: Vec<Prop>, event: Event
) {
  use std::str::from_utf8 ;
  use term::PrintSmt2 ;
  event.log(
    & format!("checking {} propertie(s) on system {}", props.len(), sys.sym())
  ) ;

  event.log("creating solver") ;

  let conf = SolverConf::z3().print_success() ;
  let factory = event.factory().clone() ;

  let mut k = Offset2::init() ;

  match Solver::mk(z3_cmd(), conf, factory.clone()) {
    Err(e) => event.log( & format!("error:\n  {:?}", e) ),
    Ok(mut solver) => {

      event.log("declaring functions") ;
      try_error!(
        sys.defclare_funs(& mut solver), event
      ) ;

      event.log("declaring state@0") ;
      try_error!(
        sys.declare_svars(& mut solver, & factory, k.curr()), event
      ) ;

      let mut s: Vec<u8> = vec![] ;
      sys.init_term().to_smt2(& mut s, & k).unwrap() ;
      let string = from_utf8(& s).unwrap() ;
      event.log( & format!("asserting init {}", string) ) ;
      try_error!(
        solver.assert( & (sys.init_term(), & k) ), event
      ) ;

      event.log("unimplemented")
    },
  }
}