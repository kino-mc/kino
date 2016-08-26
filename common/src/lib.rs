#![deny(missing_docs)]
// Copyright 2015 Adrien Champion. See the COPYRIGHT file at the top-level
// directory of this distribution.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

/*! Stuff common to all techniques.

# To do

* check that first argument of custom technique is legal

*/

extern crate ansi_term as ansi ;
#[macro_use]
extern crate nom ;
extern crate term ;
extern crate system as sys ;

use std::fmt ;
use std::sync::Arc ;

use term::{ Term, Factory } ;
use term::smt::{
  Solver, PlainSolver, TeeSolver,
  Query, QueryIdent, QueryExprInfo
} ;

use sys::{ Prop, Sys } ;

pub mod msg ;
pub mod log ;
pub mod conf ;

/** Try for `Result<T, String>`, appends something to error messages. */
#[macro_export]
macro_rules! try_str {
  ($e:expr, $($blah:expr),+) => (
    match $e {
      Ok(res) => res,
      Err(msg) => return Err(
        format!(
          "{}\n{}", format!( $($blah),+ ), msg
        )
      ),
    }
  ) ;
}


/** Solver trait that bmc and kind will use. */
pub trait SolverTrait<'a>:
  Solver<'a, Factory> +
  Query<'a, Factory> +
  QueryIdent<'a, Factory, (), String> +
  QueryExprInfo<'a, Factory, Term> {
}
impl<'a> SolverTrait<'a> for PlainSolver<'a, Factory> {}
impl<'a> SolverTrait<'a> for TeeSolver<'a, Factory> {}

/** Creates a plain solver.

```[no_use]
// With the `term` crate in scope...
mk_solver! {
  solver_conf,
  conf.smt_log(),
  "smt_log_file_name_without_smt2_extension",
  factory, // Cloned in the macro, should be a ref.
  solver => blah(conf, event, solver),
  error_msg => event.error(error_msg)
}
```

Why use a macro? The solver stores mutable references to the stdin and stout
of the kid. The kid must thus be in scope when the solver is used.

Writing this in a function is a mess, mostly because of the genericity of the
function applied in terms of `Plain`/`Tee` solvers.

# TODO

The configuration stuff to pass is messy for now, waiting for conf module to
reach maturity. */
#[macro_export]
macro_rules! mk_solver_run {
  (
    $conf:expr,
    $smt_log:expr,
    $log_file: expr,
    $factory:expr,
    $solver:ident => $run:expr,
    $err:ident => $errun:expr
  ) => (
    match term::smt::Kid::mk($conf) {
      Ok(mut kid) => match term::smt::solver(
        & mut kid, $factory.clone()
      ) {
        Ok($solver) => match * $smt_log {
          None => $run,
          Some(ref path) => {
            let path = format!("{}/{}.smt2", path, $log_file) ;
            match std::fs::File::create(& path) {
              Ok(file) => {
                let $solver = $solver.tee(file) ;
                $run
              },
              Err(e) => {
                let $err = & format!(
                  "could not open smt log file \"{}\":\n{:?}", path, e
                ) ;
                $errun
              },
            }
          },
        },
        Err(e) => {
          let $err = & format!(
            "could not create solver from kid:\n{}", e
          ) ;
          $errun
        },
      },
      Err(e) => {
        let $err = & format!(
          "could not spawn solver kid:\n{}", e
        ) ;
        $errun
      },
    }
  ) ;
}


// /** Creates a plain solver. */
// pub fn run_on_solver<
//   'a,
//   F: FnOnce(SolverTrait<'a> + 'static)
// >(
//   conf: SolverConf,
//   f: Factory,
//   run: F
// ) -> Res<()> {
//   let mut kid = try_str!(
//     Kid::mk(conf),
//     "could not spawn solver kid:"
//   ) ;
//   let solver = try_str!(
//     term::smt::solver(& mut kid, f),
//     "could not create solver from kid:"
//   ) ;
//   Ok( run(solver) )
// }

/** Result yielding a list of strings. */
pub type Res<T> = Result<T, String> ;

/** Trait the techniques should implement so that kino can call them in a
generic way. */
pub trait CanRun<Conf> {
  /** The identifier of the technique. */
  fn id(& self) -> Tek ;
  /** Runs the technique. */
  fn run(& self, Arc<Conf>, Sys, Vec<Prop>, msg::Event) ;
}

/** Enumeration of the techniques. */
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Tek {
  /** Master. */
  Kino,
  /** Bounded model checking. */
  Bmc,
  /** Induction. */
  KInd,
  /** Custom technique.
  First string is a short description that should be a legal filename.
  Second is an arbitrarily long description. */
  Tec(& 'static str, & 'static str),
}
impl fmt::Display for Tek {
  fn fmt(& self, fmt: & mut fmt::Formatter) -> fmt::Result {
    write!(fmt, "{}", self.to_str())
  }
}
impl Tek {
  /** A short string representation of a technique. */
  #[inline(always)]
  pub fn to_str(& self) -> & str {
    use Tek::* ;
    match * self {
      Kino => "master",
      Bmc => "bmc",
      KInd => "k-ind",
      Tec(ref s, _) => & s,
    }
  }
  /** A description of a technique. */
  #[inline(always)]
  pub fn desc(& self) -> & str {
    use Tek::* ;
    match * self {
      Kino => "supervisor",
      Bmc => "bounded model checking",
      KInd => "k-induction",
      Tec(_, ref desc) => & desc,
    }
  }
  /** Thread name for techniques. */
  #[inline(always)]
  pub fn thread_name(& self) -> String {
    use Tek::* ;
    match * self {
      Kino => panic!("thread name of supervisor requested"),
      Bmc => "kino_bmc".to_string(),
      KInd => "kino_k-induction".to_string(),
      Tec(ref s, _) => format!("kino_{}", s),
    }
  }
}