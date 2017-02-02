#![deny(missing_docs)]
// Copyright 2015 Adrien Champion. See the COPYRIGHT file at the top-level
// directory of this distribution.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! Stuff common to all techniques.
//!
//!# To do
//!
//! * check that first argument of custom technique is legal

extern crate ansi_term as ansi ;
#[macro_use]
extern crate nom ;
#[macro_use]
extern crate error_chain ;
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

/// Kino errors using [`error-chain`](https://crates.io/crates/error-chain).
pub mod errors {
  error_chain!{
    types {
      Error, ErrorKind, ResExt, Res ;
    }

    links {
      RSmt2(::term::errors::Error, ::term::errors::ErrorKind) #[doc = "
        An error from the [`rsmt2`](https://crates.io/crates/rsmt2) library.
      "] ;
    }

    errors {
      #[doc = "Error while spawning solver process."]
      SolverSpawnError(e: ::std::io::Error) {
        description("error while spawning solver process")
        display("could not spawn solver process: {:?}", e)
      }

      #[doc = "Error while interacting with a file."]
      FileIoError(file: String, e: ::std::io::Error) {
        description("error on file IO")
        display("error on file `{}`: {:?}", file, e)
      }

      #[doc = "Trying to spawn a technique that's already running."]
      TekDuplicateError(tek: ::Tek) {
        description("trying to spawn a technique that's already running")
        display("cannot spawn `{}`: already running", tek)
      }

      #[doc = "Trying to contact a technique that's not running."]
      TekUnknownError(tek: ::Tek) {
        description("unknown technique")
        display("technique `{}` is not running", tek)
      }

      #[doc = "Error while spawning a technique."]
      TekSpawnError(e: ::std::io::Error, tek: ::Tek) {
        description("error while trying to spawn a technique")
        display("error while spawning `{}`", tek)
      }

      #[doc = "Error while trying to receive a message."]
      MsgRcvError(tek: ::Tek) {
        description("error while trying to receive a message")
        display("error during message reception in `{}`", tek)
      }

      #[doc = "Error while sending a message."]
      MsgSndError(src: ::Tek, tgt: ::Tek) {
        description("error while sending a message")
        display("could not send message from `{}` to `{}`", src, tgt)
      }
    }
  }
}

/// Communicates an error and returns `()` if computation is an `Err`, yields
/// the result (inside the `Ok`) otherwise.
#[macro_export]
macro_rules! log_try {
  ($event:expr, $e:expr) => (
    match $e {
      Ok(res) => res,
      Err(e) => {
        $event.error(e) ;
        return ()
      },
    }
  ) ;
  ($event:expr, $e:expr => $s:expr) => (
    log_try!($event, $crate::errors::ResExt::chain_err($e, || $s))
  ) ;
  ($event:expr, $e:expr => $($fmt:expr),+ $(,)*) => (
    log_try!($event, $crate::errors::ResExt::chain_err(
      $e, || format!($($fmt),+)
    ))
  ) ;
}

/// Combines `try` and `chain_err` for strings.
#[macro_export]
macro_rules! try_chain {
  ($e:expr) => ( try!($e) ) ;
  ($e:expr => $s:expr) => (
    try_chain!($crate::errors::ResExt::chain_err($e, || $s))
  ) ;
  ($e:expr => $($fmt:expr),+ $(,)*) => (
    try_chain!($crate::errors::ResExt::chain_err($e, || format!($($fmt),+)))
  ) ;
}

pub mod msg ;
pub mod log ;
pub mod conf ;


/// Solver trait that bmc and kind will use.
pub trait SolverTrait<'a>:
  Solver<'a, Factory> +
  Query<'a, Factory> +
  QueryIdent<'a, Factory, (), String> +
  QueryExprInfo<'a, Factory, Term> {
}
impl<'a> SolverTrait<'a> for PlainSolver<'a, Factory> {}
impl<'a> SolverTrait<'a> for TeeSolver<'a, Factory> {}

/// Creates a plain solver.
/// 
/// ```[no_use]
/// // With the `term` crate in scope...
/// mk_solver! {
///   solver_conf,
///   conf.smt_log(),
///   "smt_log_file_name_without_smt2_extension",
///   factory, // Cloned in the macro, should be a ref.
///   solver => blah(conf, event, solver),
///   error => event.error(error)
/// }
/// ```
/// 
/// Why use a macro? The solver stores mutable references to the stdin and
/// stout of the kid. The kid must thus be in scope when the solver is used.
/// 
/// Writing this in a function is a mess, mostly because of the genericity of
/// the function applied in terms of `Plain`/`Tee` solvers.
/// 
/// # TODO
/// 
/// The configuration stuff to pass is messy for now, waiting for conf module
/// to reach maturity.
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
    match $crate::errors::ResExt::chain_err(
      term::smt::Kid::mk($conf),
      || "while spawning solver kid"
    ) {
      Ok(mut kid) => match $crate::errors::ResExt::chain_err(
        term::smt::solver(
          & mut kid, $factory.clone()
        ), || "while creating solver from kid"
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
                use $crate::errors::Res ;
                let e: Res<()> = Err(
                  $crate::errors::ErrorKind::FileIoError(path, e).into()
                ) ;
                let $err = $crate::errors::ResExt::chain_err(
                  e, || "while creating SMT solver tee file"
                ).unwrap_err() ;
                $errun
              },
            }
          },
        },
        Err($err) => $errun,
      },
      Err($err) => $errun,
    }
  ) ;
}
/// Same as [`mk_solver_run`](macro.mk_solver_run!.html) with two solvers.
#[macro_export]
macro_rules! mk_two_solver_run {
  (
    $conf:expr,
    $smt_log:expr,
    $log_file: expr,
    $factory:expr,
    (
      $solver1:ident $log_suff1:expr, $solver2:ident $log_suff2:expr
    ) => $run:expr,
    $err:ident => $errun:expr
  ) => (
    match (
      $crate::errors::ResExt::chain_err(
        term::smt::Kid::mk($conf.clone()),
        || format!("while creating {} solver kid", $log_suff1)
      ), $crate::errors::ResExt::chain_err(
        term::smt::Kid::mk($conf),
        || format!("while creating {} solver kid", $log_suff2)
      )
    ) {
      ( Ok(mut kid_1), Ok(mut kid_2) ) => match (
        $crate::errors::ResExt::chain_err(
          term::smt::solver( & mut kid_1, $factory.clone() ),
          || format!("while creating {} solver of kid", $log_suff1)
        ),
        $crate::errors::ResExt::chain_err(
          term::smt::solver( & mut kid_2, $factory.clone() ),
          || format!("while creating {} solver of kid", $log_suff2)
        ),
      ) {
        ( Ok($solver1), Ok($solver2) ) => match * $smt_log {
          None => $run,
          Some(ref path) => {
            use $crate::errors::Res ;
            let (path_1, path_2) = (
              format!("{}/{}_{}.smt2", path, $log_file, $log_suff1),
              format!("{}/{}_{}.smt2", path, $log_file, $log_suff2)
            ) ;
            match (
              std::fs::File::create(& path_1),
              std::fs::File::create(& path_2)
            ) {
              (Ok(file_1), Ok(file_2)) => {
                let $solver1 = $solver1.tee(file_1) ;
                let $solver2 = $solver2.tee(file_2) ;
                $run
              },
              (Err(e), _) => {
                let e: $crate::errors::Error =
                  $crate::errors::ErrorKind::FileIoError(path_1, e).into() ;
                let e: Res<()> = Err(e) ;
                let $err = $crate::errors::ResExt::chain_err(
                  e, || "while creating SMT solver tee file"
                ).unwrap_err() ;
                $errun
              },
              (_, Err(e)) => {
                let e: $crate::errors::Error =
                  $crate::errors::ErrorKind::FileIoError(path_2, e).into() ;
                let e: Res<()> = Err(e) ;
                let $err = $crate::errors::ResExt::chain_err(
                  e, || "while creating SMT solver tee file"
                ).unwrap_err() ;
                $errun
              },
            }
          },
        },
        (Err($err), _) => $errun,
        (_, Err($err)) => $errun,
      },
      (Err($err), _) => $errun,
      (_, Err($err)) => $errun,
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

/// Trait the techniques should implement so that kino can call them in a
/// generic way.
pub trait CanRun<Conf> {
  /// The identifier of the technique.
  fn id(& self) -> Tek ;
  /// Runs the technique.
  fn run(& self, Arc<Conf>, Sys, Vec<Prop>, msg::Event) ;
}

/// Enumeration of the techniques.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Tek {
  /// Master.
  Kino,
  /// Bounded model checking.
  Bmc,
  /// K-induction.
  KInd,
  /// 2-induction.
  Twind,
  /// Invgen.
  Tig,
  /// Invariant pruner.
  Pruner,
  /// Custom technique.
  /// First string is a short description that should be a legal filename.
  /// Second is an arbitrarily long description.
  Tec(& 'static str, & 'static str),
}
impl fmt::Display for Tek {
  fn fmt(& self, fmt: & mut fmt::Formatter) -> fmt::Result {
    write!(fmt, "{}", self.to_str())
  }
}
impl Tek {
  /// A short string representation of a technique.
  #[inline(always)]
  pub fn to_str(& self) -> & str {
    use Tek::* ;
    match * self {
      Kino => "master",
      Bmc => "bmc",
      KInd => "k-ind",
      Twind => "2-ind",
      Tig => "tig",
      Pruner => "pruner",
      Tec(ref s, _) => & s,
    }
  }
  /// A description of a technique.
  #[inline(always)]
  pub fn desc(& self) -> & str {
    use Tek::* ;
    match * self {
      Kino => "supervisor",
      Bmc => "bounded model checking",
      KInd => "k-induction",
      Twind => "2-induction",
      Tig => "invariant generation",
      Pruner => "invariant pruner",
      Tec(_, ref desc) => & desc,
    }
  }
  /// Thread name for techniques.
  #[inline(always)]
  pub fn thread_name(& self) -> String {
    use Tek::* ;
    match * self {
      Kino => panic!("thread name of supervisor requested"),
      Bmc => "kino_bmc".to_string(),
      KInd => "kino_k-induction".to_string(),
      Twind => "kino_2-induction".to_string(),
      Tig => "kino_invgen".to_string(),
      Pruner => "kino_pruner".to_string(),
      Tec(ref s, _) => format!("kino_{}", s),
    }
  }
}