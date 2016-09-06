// Copyright 2015 Adrien Champion. See the COPYRIGHT file at the top-level
// directory of this distribution.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

#![deny(missing_docs)]

//! Tinelli-style invariant generation.

extern crate term ;
extern crate system ;
#[macro_use]
extern crate common ;
extern crate unroll ;

use std::sync::Arc ;
use std::fmt::Display ;

use term::{
  Factory, Term, TermSet,
  Cst, Bool, Int, Rat, Offset,
  STerm, STermSet
} ;
use term::tmp::{ TmpTerm, TmpTermSet, TmpTermMap } ;

use system::{ Sys, Prop } ;

use common::{ Res, SolverTrait, CanRun } ;
use common::msg::Event ;
use common::conf ;

pub mod eval ;
pub mod mine ;
pub mod chain ;
pub mod graph ;
pub mod lsd ;


/// Invgen technique.
pub struct Tig ;
unsafe impl Send for Tig {}
impl CanRun<conf::Tig> for Tig {
  fn id(& self) -> common::Tek { common::Tek::Tig }

  fn run(
    & self, conf: Arc<conf::Tig>, sys: Sys, _: Vec<Prop>, mut event: Event
  ) {
    // event.log("starting invgen") ;

    let mut solver_conf = conf.smt().clone().default().print_success() ;
    match * conf.smt_cmd() {
      None => (),
      Some(ref cmd) => solver_conf = solver_conf.cmd(cmd.clone()),
    } ;

    mk_solver_run!(
      solver_conf, conf.smt_log(), "tig", event.factory(),
      solver => invgen(* conf.max(), solver, sys, & mut event),
      msg => event.error(msg)
    )
  }
}


/// Runs invgen.
fn invgen<
  'a, S: SolverTrait<'a>
>(
  max_k: Option<usize>, solver: S, sys: Sys, event: & mut Event
) {
  use graph::* ;
  use lsd::top_only::* ;

  let graph_dir = "graph" ;
  // if ! try_error!(
  //   ::std::fs::metadata(graph_dir), event,
  //   "unable to retrieve information about graph log directory `{}`", graph_dir
  // ).is_dir()
  {
    use std::fs::DirBuilder ;
    let mut db = DirBuilder::new() ;
    db.recursive(true) ;
    try_error!(
      db.create(graph_dir), event,
      "while creating directory `{}` for graph logging", graph_dir
    )
  } ;

  let factory = solver.parser().clone() ;

  // event.log("mining system") ;
  let (rep, class) = mine::bool(& factory, & sys) ;

  // let mut blah = format!("{} ->", rep) ;
  // for t in class.iter() {
  //   blah = format!("{}\n    {}", blah, t)
  // } ;
  // event.log(& blah) ;

  // event.log("creating graph") ;
  let mut graph = Graph::<Bool>::mk(rep, class) ;

  // event.log("creating base checker") ;
  let mut base = try_error!(
    Base::mk(& sys, solver, 0), event,
    "while creating base checker"
  ) ;

  let mut cnt = 1 ;

  let mut known = TmpTermSet::with_capacity(103) ;

  'work: while max_k.map_or(true, |max| cnt <= max) {
    event.log( & format!("starting invgen with {} unrollings", cnt) ) ;
    // event.log( & format!("starting base stabilization ({})", cnt) ) ;
    
    let mut base_cnt = 0 ;

    'base: loop {
      let candidates: Vec<TmpTerm> = graph.candidates(
        |cand| known.contains(cand)
      ).into_iter().collect() ;
      if candidates.is_empty() {
        event.log(
          & format!(
            "on {} at {}\n\
            no non-trivial candidate in the graph\n\
            graph is stale, stopping",
            sys.sym(), cnt
          )
        ) ;
        break 'work
      }
      match try_error!(
        base.k_falsify(candidates), event,
        "while looking for {}-falsification ({})", cnt, base_cnt
      ) {
        Some(eval) => try_error!(
          graph.split(eval), event,
          "while splitting graph in base at {}, {}", cnt, base_cnt
        ),
        None => break 'base,
      }
      
      // let file_path = format!("{}/tig_{}_{}.dot", graph_dir, cnt, base_cnt) ;
      // try_error!(
      //   graph.dot_dump( & file_path ), event,
      //   "could not dump graph to file `{}`", file_path
      // ) ;
      base_cnt += 1
    }

    // event.log(
    //   & format!("done stabilizing in base ({})", cnt)
    // ) ;

    let candidates: TmpTermMap<()> = try_error!(
      graph.all_candidates( |cand| known.contains(cand) ), event,
      "while generating all candidates of graph ({})", cnt
    ).into_iter().map(
      |cand| (cand, ())
    ).collect() ;

    try_error!(
      base.unroll(), event,
      "could not unroll base checker ({})", cnt
    ) ;

    // event.log(
    //   & format!(
    //     "extracting invariants from {} candidates ({})", candidates.len(), cnt
    //   )
    // ) ;

    let mut step = try_error!(
      base.to_step(), event,
      "could not morph base checker to step checker ({})", cnt
    ) ;

    let candidate_count = candidates.len() ;

    let (invars, _) = try_error!(
      step.k_split(candidates), event,
      "could not k-split {} candidates in step ({})", candidate_count, cnt
    ) ;
    let invar_count = invars.len() ;

    let mut invariants = STermSet::with_capacity(invars.len()) ;
    for (invar, _) in invars.into_iter() {
      known.insert(invar.clone()) ;
      use term::UnTermOps ;
      let invar = try_error!(
        invar.to_term_safe(& factory), event,
        "could not turn tmp term in term"
      ) ;
      invariants.insert(
        STerm::One(
          try_error!(
            factory.debump(& invar), event,
            "could not debump term {}", invar
          ),
          invar
        )
      ) ;
      ()
    }
    if ! invariants.is_empty() {
      event.invariants(sys.sym(), invariants)
    }

    // let blah = format!(
    //   "on {} at {}\n\
    //   found {} invariants for system {} from {} candidates",
    //   sys.sym(), cnt,
    //   invar_count, sys.sym(), candidate_count
    // ) ;
    // for (term, _) in invars.iter() {
    //   blah = format!("{}\n  - {}", blah, term)
    // }
    // event.log( & blah ) ;

    if invar_count == candidate_count {
      // Everything's invariant, stopping.
      event.log(
        & format!(
          "on {} at {}\n\
          all terms encoded by the graph have been proved invariant\n\
          stopping",
          sys.sym(), cnt
        )
      ) ;
      break 'work
    }

    base = try_error!(
      step.to_base(), event,
      "could not morph step checker to base checker ({})", cnt
    ) ;

    cnt += 1 ;

    ()

  }

  event.done_at( & Offset::of_int(cnt) ) ;
}








/** Trait for domains.

Domains define the type of the values the candidate terms evaluate to and a
total order relation used for the edges in the graph. */
pub trait Domain : PartialEq + Eq + PartialOrd + Ord + Clone + Display {
  /// A value from a constant.
  fn of_cst(& Cst) -> Result<Self, String> ;
  /// Creates a term encoding a relation between terms.
  fn mk_cmp(& Term, & Term) -> Option<TmpTerm> ;
  /// Creates a term encoding an equality between terms.
  fn mk_eq(& Term, & Term) -> Option<TmpTerm> ;
  /// Creates a term encoding a relation between terms.
  fn insert_cmp<
    Ignore: Fn(& TmpTerm) -> bool
  >(lhs: & Term, rhs: & Term, set: & mut TmpTermSet, ignore: Ignore) {
    if let Some( term ) = Self::mk_cmp(lhs, rhs) {
      if ! ignore(& term) { set.insert(term) ; () }
    }
  }
  /// Creates a term encoding an equality between terms.
  fn insert_eq<
    Ignore: Fn(& TmpTerm) -> bool
  >(lhs: & Term, rhs: & Term, set: & mut TmpTermSet, ignore: Ignore) {
    if let Some( term ) = Self::mk_eq(lhs, rhs) {
      if ! ignore(& term) { set.insert(term) ; () }
    }
  }
  /// Chooses a representative in a set, removes it from the set.
  fn choose_rep(& Factory, TermSet) -> Res<(Term, TermSet)> ;
}
impl Domain for Bool {
  fn of_cst(cst: & Cst) -> Result<Self, String> {
    match * cst.get() {
      ::term::real_term::Cst::Bool(b) => Ok(b),
      ref cst => Err(
        format!("[Bool::of_cst] unexpected constant {}", cst)
      ),
    }
  }
  fn mk_cmp(lhs: & Term, rhs: & Term) -> Option<TmpTerm> {
    if ! lhs.is_false() && ! rhs.is_true() {
      Some( TmpTerm::mk_term_impl(lhs.clone(), rhs.clone()) )
    } else {
      None
    }
  }
  fn mk_eq(lhs: & Term, rhs: & Term) -> Option<TmpTerm> {
    Some( TmpTerm::mk_term_eq(lhs.clone(), rhs.clone()) )
  }
  fn choose_rep(
    factory: & Factory, mut set: TermSet
  ) -> Res<(Term, TermSet)> {
    use term::CstMaker ;
    let tru = factory.cst(true) ;
    let was_there = set.remove(& tru) ;
    if was_there {
      Ok( (tru, set) )
    } else {
      let rep = match set.iter().next() {
        Some(rep) => rep.clone(),
        None => return Err(
          format!(
            "[Bool::choose_rep] cannot choose representative of empty set"
          )
        ),
      } ;
      let was_there = set.remove(& rep) ;
      debug_assert!( was_there ) ;
      Ok( (rep, set) )
    }
  }
}
impl Domain for Int  {
  fn of_cst(cst: & Cst) -> Result<Self, String> {
    match * cst.get() {
      ::term::real_term::Cst::Int(ref i) => Ok(i.clone()),
      ref cst => Err(
        format!("[Int::of_cst] unexpected constant {}", cst)
      ),
    }
  }
  fn mk_cmp(lhs: & Term, rhs: & Term) -> Option<TmpTerm> {
    Some( TmpTerm::mk_term_le(lhs.clone(), rhs.clone()) )
  }
  fn mk_eq(lhs: & Term, rhs: & Term) -> Option<TmpTerm> {
    Some( TmpTerm::mk_term_eq(lhs.clone(), rhs.clone()) )
  }
  fn choose_rep(_: & Factory, mut set: TermSet) -> Res<(Term, TermSet)> {
    let rep = match set.iter().next() {
      Some(rep) => rep.clone(),
      None => return Err(
        format!(
          "[Int::choose_rep] cannot choose representative of empty set"
        )
      ),
    } ;
    let was_there = set.remove(& rep) ;
    debug_assert!( was_there ) ;
    Ok( (rep, set) )
  }
}
impl Domain for Rat  {
  fn of_cst(cst: & Cst) -> Result<Self, String> {
    match * cst.get() {
      ::term::real_term::Cst::Rat(ref r) => Ok(r.clone()),
      ref cst => Err(
        format!("[Rat::of_cst] unexpected constant {}", cst)
      ),
    }
  }
  fn mk_cmp(lhs: & Term, rhs: & Term) -> Option<TmpTerm> {
    Some( TmpTerm::mk_term_le(lhs.clone(), rhs.clone()) )
  }
  fn mk_eq(lhs: & Term, rhs: & Term) -> Option<TmpTerm> {
    Some( TmpTerm::mk_term_eq(lhs.clone(), rhs.clone()) )
  }
  fn choose_rep(_: & Factory, mut set: TermSet) -> Res<(Term, TermSet)> {
    let rep = match set.iter().next() {
      Some(rep) => rep.clone(),
      None => return Err(
        format!(
          "[Rat::choose_rep] cannot choose representative of empty set"
        )
      ),
    } ;
    let was_there = set.remove(& rep) ;
    debug_assert!( was_there ) ;
    Ok( (rep, set) )
  }
}