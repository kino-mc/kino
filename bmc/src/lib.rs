extern crate term ;
extern crate event ;
extern crate system ;

use term::smt::* ;

use event::Event ;

use system::{ CallSet, Callable, Sys, Prop } ;

pub fn run(
  sys: Sys, props: Vec<Prop>, event: Event
) {
  event.log(
    & format!("checking {} propertie(s) on system {}", props.len(), sys.sym())
  ) ;

  event.log("creating solver") ;

  let conf = SolverConf::z3().print_success() ;
  let factory = event.factory().clone() ;
  match Solver::mk(z3_cmd(), conf, factory.clone()) {
    Err(e) => event.log( & format!("error:\n  {:?}", e) ),
    Ok(mut solver) => {

      event.log("declaring functions") ;

      for fun in sys.calls() {
        match * * fun {
          system::real::Callable::Dec(ref fun) => {
            event.log( & format!("declaring {}", fun) ) ;
            match solver.declare_fun(
              fun.sym().get(), & vec![], fun.typ().clone()
            ) {
              Ok(()) => event.log("succes"),
              Err(e) => event.log( & format!("error: {:?}", e) ),
            }
          },
          system::real::Callable::Def(ref fun) => {
            event.log( & format!("defining {}", fun) ) ;
          },
        }
      } ;

      event.log("unimplemented")
    },
  }
}