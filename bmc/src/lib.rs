extern crate term ;
extern crate event ;
extern crate system ;

use term::Offset2 ;
use term::smt::* ;
use term::smt::sync::* ;

use event::Event ;

use system::{ Sys, Prop } ;
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
  use term::{ Operator, SymMaker, OpMaker, VarMaker, Type } ;
  event.log(
    & format!("checking {} propertie(s) on system {}", props.len(), sys.sym())
  ) ;

  event.log("creating solver") ;

  let conf = SolverConf::z3().print_success() ;
  let factory = event.factory().clone() ;

  let k = Offset2::init() ;

  match Solver::mk(z3_cmd(), conf, factory.clone()) {
    Err(e) => event.log( & format!("error:\n  {:?}", e) ),
    Ok(mut solver) => {

      event.log("declaring functions, init and trans") ;
      try_error!(
        sys.defclare_funs(& mut solver), event
      ) ;

      event.log("declaring state@0") ;
      try_error!(
        sys.declare_svars(& mut solver, & factory, k.curr()), event
      ) ;

      event.log( "asserting init@0" ) ;
      try_error!(
        solver.assert( & (sys.init_term(), & k) ), event
      ) ;

      let cpt = 0 ;

      loop {

        let actlit = factory.sym(format!("fresh_{}", cpt)) ;
        let actlit = factory.var_consign().var( actlit ) ;
        let mut neg_props = Vec::with_capacity(props.len()) ;
        for prop in props.iter() {
          neg_props.push(
            factory.op(
              Operator::Not, vec![prop.body().clone()]
            )
          )
        }
        let prop_term = factory.op(
          Operator::Or, neg_props
        ) ;
        event.log(
          & format!("defining actlit {}\nto imply {}", actlit, prop_term)
        ) ;

        try_error!(
          solver.declare_fun(
            & (& actlit, k.curr()),
            & Vec::<Type>::new(),
            & Type::Bool
          ), event
        ) ;

        let e = factory.op(
          Operator::Impl, vec![
            factory.mk_var(actlit.clone()),
            prop_term
          ]
        ) ;

        try_error!(
          solver.assert(& (& e, & k)), event
        ) ;

        event.log(
          & format!("check-sat assuming {}", actlit)
        ) ;

        match solver.check_sat_assuming( & vec![(& actlit, k.curr())] ) {
          Ok(true) => event.log("sat"),
          Ok(false) => event.log("unsat"),
          Err(e) => event.log( & format!("{:?}", e) ),
        } ;

        event.log("unrolling is not implemented, exiting") ;

        break

      }
    },
  }
}