// Copyright 2016 Adrien Champion. See the COPYRIGHT file at the top-level
// directory of this distribution.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

/*! Graph representing the knowledge learnt by the invariant generation
technique. */

use std::io ;

use common::Res ;
use common::msg::Event ;
use common::conf ;

use term::{
  Sym, Factory, Term, TermSet, TermMap, Bool
} ;
use term::tmp::{ TmpTerm, TmpTermSet, TmpTermMap } ;

use system::Sys ;

use Domain ;
use eval::Eval ;
use chain::* ;
use lsd::* ;
use mine ;


/// Map from representatives to their class.
pub type Classes = TermMap< TermSet > ;

/// Map from representatives to their kids/parents.
pub type Edges = TermMap< TermSet > ;

/// Candidate invariant info.
///
/// Stores the information needed to drop a term from an equivalence class:
/// the representative of the class and the term to drop.
///
/// This is used when generating candidates from equivalence classes. If the
/// candidate is indeed invariant, then the rhs of the equality can be dropped
/// from the class it belongs to.
///
/// Candidates from edges just store `None`.
pub type CandInfo = Option<(Term, Term)> ;

/// A set of candidate invariants.
pub type Candidates = TmpTermMap< CandInfo > ;


/// Can check itself.
pub trait CanCheck {
  /// Checks itself (in `debug`).
  #[cfg( debug_assertions )]
  #[inline]
  fn check(& self) -> Res<()> ;
  /// Does nothing (in `release`).
  #[cfg( not(debug_assertions) )]
  #[inline(always)]
  fn check(& self) -> Res<()> {
    Ok(())
  }
}

/// Can stabilize itself given an evaluator.
pub trait CanStabilize {
  /// Underlying domain of the graph.
  type Val: Domain ;
  /// Stabilizes itself given an evaluator.
  fn split(& mut self, & mut Eval< Self::Val >) -> Res<()> ;
}

/// Can log itself.
pub trait CanLog {
  /// Logs itself to some file with `dot` extension.
  fn log_to(& self, & str) -> Res<()> ;
}

/// Has equivalence classes.
pub trait HasClasses: CanStabilize + CanLog {
  /// Creates a `Self` from a system and a single class given as a
  /// representative and the members of the class.
  fn mk(rep: Term, class: TermSet) -> Self ;
  /// The equivalence classes.
  #[inline]
  fn classes(& self) -> & Classes ;
  /// Equivalence class of a representative.
  #[inline]
  fn class_of(& self, rep: & Term) -> Res<& TermSet> {
    Ok(
      try_str_opt!(
        self.classes().get(rep),
        "[HasClasses::class_of] \
        unknown rep `{}`", rep
      )
    )
  }
  /// Checks the equivalence classes of a graph.
  ///
  /// Checks that
  /// - no term appears in two equivalence classes;
  /// - no representative appears in a class.
  #[inline]
  fn check_classes(& self) -> Res<()> {
    use std::collections::{ HashSet, HashMap } ;
    let mut reps = HashSet::with_capacity( self.classes().len() ) ;
    let mut trms = HashMap::with_capacity( self.classes().len() * 10 ) ;

    for (rep, class) in self.classes().iter() {
      // Is `rep` a member of some other class?
      if let Some(rep_bis) = trms.get(rep) {
        error!(
          "rep `{}` is also a member of the class of `{}`", rep, rep_bis
        )
      }
      let wasnt_there = reps.insert(rep) ;
      assert!( wasnt_there ) ;
      for trm in class.iter() {
        // Is `trm` also a representative?
        if reps.contains(trm) {
          error!(
            "rep `{}` is also a member of the class of `{}`", trm, rep
          )
        }
        // Is `trm` in another class?
        if let Some(rep_bis) = trms.insert(trm, rep) {
          error!(
            "term `{}` is a member of both `{}` and `{}`", trm, rep, rep_bis
          )
        }
      }
    }

    Ok(())
  }

  /// The equivalence classes, mutable version.
  #[inline]
  fn mut_classes(& mut self) -> & mut Classes ;
  /// Equivalence class of a representative.
  #[inline]
  fn mut_class_of(& mut self, rep: & Term) -> Res<& mut TermSet> {
    Ok(
      try_str_opt!(
        self.mut_classes().get_mut(rep),
        "[HasClasses::mut_class_of] \
        unknown rep `{}`", rep
      )
    )
  }
  /// Drops a term from an equivalence class.
  #[inline]
  fn drop_term(& mut self, rep: & Term, trm: & Term) -> Res<bool> {
    Ok(
      try_str!(
        self.mut_class_of(rep),
        "[HasClasses::drop_term] \
        while dropping term `{}` from `{}`", trm, rep
      ).remove(trm)
    )
  }

  /// Terms for the equality chain between members of a class.
  ///
  /// None if class is a singleton.
  fn base_cands_of_class(
    & self, rep: & Term, known: & TmpTermSet
  ) -> Res< Option< Vec<TmpTerm> > > {
    let class = try_str!(
      self.class_of(rep),
      "[HasClasses::base_cands_of_class] \
      while retrieving class of `{}`", rep
    ) ;
    // Early return if class is empty.
    if class.is_empty() {
      return Ok( None )
    }

    let mut terms = Vec::with_capacity(class.len()) ;
    for term in class.iter() {
      if let Some(eq) = Self::Val::mk_eq(rep, term) {
        if ! known.contains(& eq) { terms.push( eq ) }
      }
    }
    Ok( Some(terms) )
  }

  /// Candidate terms encoding all equalities between members of a class.
  ///
  /// Actually depends on the cardinality of `rep`'s class. If it's too big,
  /// then only equalities with the representative are produced.
  ///
  /// Each candidate term is mapped to a pair `(rep, term)` with the semantics
  /// that if a candidate term is invariant, then `term` can be dropped from
  /// the class of `rep`.
  ///
  /// Returns true iff some new candidates were generated.
  fn step_cands_of_class(
    & self, rep: & Term, candidates: & mut Candidates, known: & TmpTermSet
  ) -> Res<bool> {
    let rep_class = try_str!(
      self.class_of(rep),
      "[HasClasses::step_cands_of_class] \
      while retrieving class of `{}`", rep
    ) ;
    // Early return if class is empty.
    if rep_class.is_empty() {
      return Ok( false )
    }

    let generate_all = rep_class.len() <= 7 ;

    let mut iter = rep_class.iter() ;
    // Generate all terms.
    while let Some(term) = iter.next() {
      if let Some(eq) = Self::Val::mk_eq(rep, term) {
        if ! known.contains(& eq) {
          let previous = candidates.insert(
            eq, Some( (rep.clone(), term.clone()) )
          ) ;
          debug_assert!( previous.is_none() )
        }
      }
      if generate_all {
        for trm in iter.clone() {
          if let Some(eq) = Self::Val::mk_eq(term, trm) {
            if ! known.contains(& eq) {
              let previous = candidates.insert(
                eq, Some( (rep.clone(), trm.clone()) )
              ) ;
              debug_assert!( previous.is_none() )
            }
          }
        }
      }
    }
    Ok( true )
  }
}

/// Has no edges, equivalence classes only.
pub trait HasNoEdges : HasClasses {
  /// Extracts a representative for an unstable class, if any.
  fn choose_unstable(& self, stable: & TermSet) -> Option< & Term > {
    for (rep, _) in self.classes() {
      if ! stable.contains(rep) {
        return Some( rep )
      }
    }
    None
  }
}

/// Has edges.
pub trait HasEdges : HasClasses {
  /// The forward edges.
  #[inline]
  fn edges_for(& self) -> & Edges ;
  /// The forward edges, mutable version.
  #[inline]
  fn mut_edges_for(& mut self) -> & mut Edges ;
  /// The kids of a representative.
  #[inline]
  fn kids_of(& self, rep: & Term) -> Res< & TermSet > {
    Ok(
      try_str_opt!(
        self.edges_for().get(rep),
        "[HasEdges::kids_of] unknown rep `{}`", rep
      )
    )
  }

  /// The backward edges.
  #[inline]
  fn edges_bak(& self) -> & Edges ;
  /// The backward edges, mutable version.
  #[inline]
  fn mut_edges_bak(& mut self) -> & mut Edges ;
  /// The parents of a representative.
  #[inline]
  fn parents_of(& self, rep: & Term) -> Res< & TermSet > {
    Ok(
      try_str_opt!(
        self.edges_bak().get(rep),
        "[HasEdges::parents_of] unknown rep `{}`", rep
      )
    )
  }

  /// Checks the edges of a graph.
  ///
  /// Checks that
  /// - all representatives are defined in `edges_for` and `edges_bak`;
  /// - `rep -> kid` in `edges_for` iff `kid -> rep` in `edges_bak`.
  #[inline]
  fn check_edges(& self) -> Res<()> {
    // All representatives defined.
    for (rep, _) in self.classes().iter() {
      if ! self.edges_for().contains_key(rep) {
        error!(
          "rep `{}`\nis not defined in kid map", rep
        )
      }
      if ! self.edges_bak().contains_key(rep) {
        error!(
          "rep `{}`\nis not defined in parent map", rep
        )
      }
    }
    // `rep -> kid` => `kid <- rep`
    for (rep, kids) in self.edges_for().iter() {
      for kid in kids.iter() {
        if let Ok( parents ) = self.parents_of(kid) {
          if ! parents.contains(rep) {
            error!(
              "kid `{}`\nof `{}`\n\
              inverse relation not found in parent map", kid, rep
            )
          }
        } else {
          error!(
            "kid `{}`\nof `{}`\n\
            undefined in parent map", kid, rep
          )
        }
      }
    }
    // `rep <- parent` => `parent -> rep`
    for (rep, parents) in self.edges_bak().iter() {
      for parent in parents.iter() {
        if let Ok( kids ) = self.kids_of(parent) {
          if ! kids.contains(rep) {
            error!(
              "parent `{}`\nof `{}`\n\
              inverse relation not found in kid map", parent, rep
            )
          }
        } else {
          error!(
            "parent `{}`\nof `{}`\n\
            undefined in kid map", parent, rep
          )
        }
      }
    }
    Ok(())
  }

  /// Terms for the relations between a representative and its parents.
  ///
  /// None if rep has no parents.
  fn base_cands_of_edges(
    & self, rep: & Term, known: & mut TmpTermSet
  ) -> Res< Option< Vec<TmpTerm> > > {
    let parents = try_str!(
      self.parents_of(rep),
      "[HasEdges::base_cands_of_edges] \
      while retrieving parents of `{}`", rep
    ) ;

    // Early return if class is empty.
    if parents.is_empty() {
      return Ok( None )
    }

    let mut terms = Vec::with_capacity(parents.len()) ;
    for parent in parents.iter() {
      if let Some(cmp) = Self::Val::mk_cmp(parent, rep) {
        if ! known.contains(& cmp) {
          terms.push( cmp )
        }
      }
    }
    Ok(
      if ! terms.is_empty() {
        terms.shrink_to_fit() ;
        Some(terms)
      } else {
        None
      }
    )
  }

  /// Candidate terms encoding all edges between members of a class.
  ///
  /// Actually depends on the cardinality of `rep`'s class, and that of its
  /// parents. When a class is too big, then it is ignored and only edges
  /// from/to the representative are considered.
  ///
  /// Candidate terms are mapped to `()` since we don't want to remember
  /// anything about them. Info is for equivalences, where we can drop one a
  /// term from the class.
  fn step_cands_of_edges(
    & self, rep: & Term, candidates: & mut Candidates, known: & TmpTermSet
  ) -> Res<bool> {
    let err_pref = "[HasEdges::step_cands_of_edges]" ;
    let rep_parents = try_str!(
      self.parents_of(rep),
      "{} while retrieving parents of `{}`", err_pref, rep
    ) ;
    let rep_class = try_str!(
      self.class_of(rep),
      "{} while retrieving class of `{}`", err_pref, rep
    ) ;
    // Early return if no parents.
    if rep_parents.is_empty() {
      return Ok( false )
    }

    let rep_generate_all = rep_class.len() <= 7 ;

    // Generate all terms.
    for parent in rep_parents.iter() {
      if let Some(cmp) = Self::Val::mk_cmp(parent, rep) {
        if ! known.contains(& cmp) {
          let previous = candidates.insert(cmp, None) ;
          debug_assert!( previous.is_none() )
        }
      }
      for term in rep_class.iter() {
        if let Some(cmp) = Self::Val::mk_cmp(parent, term) {
          if ! known.contains(& cmp) {
            let previous = candidates.insert(cmp, None) ;
            debug_assert!( previous.is_none() )
          }
        }
      }
      let parent_class = try_str!(
        self.class_of(parent),
        "{} while retrieving class of `{}`, parent of `{}`",
        err_pref, parent, rep
      ) ;

      let parent_generate_all = parent_class.len() <= 10 ;

      for parent_term in parent_class.iter() {
        if let Some(cmp) = Self::Val::mk_cmp(parent_term, rep) {
          if ! known.contains(& cmp) {
            let previous = candidates.insert(cmp, None) ;
            debug_assert!( previous.is_none() )
          }
        }

        if rep_generate_all && parent_generate_all {
          for term in rep_class.iter() {
            if let Some(cmp) = Self::Val::mk_cmp(parent_term, term) {
              if ! known.contains(& cmp) {
                let previous = candidates.insert(cmp, None) ;
                debug_assert!( previous.is_none() )
              }
            }
          }
        }
      }
    }
    Ok( true )
  }

  /// Returns all the step terms for the graph. Equivalent to calling
  /// `step_cands_of_class` and `step_cands_of_edges` on all classes.
  fn step_cands(
    & self, candidates: & mut Candidates, known: & mut TmpTermSet
  ) -> Res<bool> {
    let err_pref = "[HasEdges::step_cands]" ;
    let mut new_stuff = false ;
    for (rep, _) in self.classes().into_iter() {
      new_stuff = new_stuff || try_str!(
        self.step_cands_of_class(rep, candidates, known),
        "{} during extraction of class candidates for rep `{}`", err_pref, rep
      ) ;
      new_stuff = new_stuff || try_str!(
        self.step_cands_of_edges(rep, candidates, known),
        "{} during extraction of edge candidates for rep `{}`", err_pref, rep
      )
    }
    Ok( new_stuff )
  }
}

impl<T: HasEdges> CanCheck for T {
  #[cfg(debug_assertions)]
  fn check(& self) -> Res<()> {
    let res = match self.check_classes() {
      Ok(()) => self.check_edges(),
      err => err
    } ;
    match res {
      Ok(()) => Ok(()),
      Err(mut e) => {
        let file = format!("error_graph") ;
        match self.log_to(& file) {
          Ok(()) => e = format!(
            "{}\n(graph dumped as `{}`)", e, file
          ),
          Err(err) => e = format!(
            "{}\ncould not dump graph as `{}`:\n{}", e, file, err
          ),
        }
        Err(e)
      },
    }
  }
}



/// Wraps a graph to create a learner.
pub struct Learner<Graph: HasClasses> {
  /// System's identifier.
  sys: Sym,
  /// The underlying graph.
  graph: Graph,
  /// `TmpTerm`s known to be invariants.
  known: TmpTermSet,
  /// Stable representatives.
  stable: TermSet,
  /// Factory, for `TmpTerm` transformation.
  factory: Factory,
  /// Previous candidate invariants to check again.
  candidates: TmpTermMap< Option< (Term, Term) > >,
  /// Activates early eq invariant discovery.
  early_eqs: bool,
  /// Activates early cmp invariant discovery.
  early_cmps: bool,
}

impl<Graph: HasClasses> CanLog for Learner<Graph> {
  fn log_to(& self, path: & str) -> Res<()> {
    self.graph.log_to(path)
  }
}

impl<
  Graph: HasClasses + CanCheck + CanStabilize
> Learner<Graph> {

  /// Creates a `Learner` from
  /// - a system,
  /// - a single class given as a representative and the members of the class,
  /// - a factory for `TmpTerm` conversion,
  /// - a `Tig` configuration.
  pub fn mk(
    sys: Sys, rep: Term, class: TermSet, factory: Factory, conf: & conf::Tig
  ) -> Self {
    Learner {
      sys: sys.sym().clone(),
      graph: Graph::mk(rep, class),
      known: TmpTermSet::with_capacity(211),
      stable: TermSet::with_capacity(17),
      factory: factory,
      candidates: TmpTermMap::with_capacity(211),
      early_eqs: * conf.early_eqs(),
      early_cmps: * conf.early_cmps(),
    }
  }

  /// Clears the internal caches and memories of the learner.
  ///
  /// Must be called between increments of the lock-step driver.
  pub fn clear(& mut self) -> () {
    self.candidates.clear() ;
    self.stable.clear()
  }

  /// Number of candidates in the underlying graph.
  pub fn len(& self) -> usize {
    let mut res = 0 ;
    for (_, class) in self.graph.classes().iter() {
      res += class.len() + 1
    }
    res
  }


  /// Receives invariants, updates the checkers.
  fn recv<Base, Step>(
    & mut self, base: & mut Base, step: & mut Step, event: & mut Event
  ) -> Res<()> where
  Base: BaseTrait<Graph::Val, Step>,
  Step: StepTrait<Graph::Val, Base> {
    use common::msg::MsgDown ;

    let err_pref = "[Learner::recv]" ;

    match event.recv() {
      None => (),
      Some(msgs) => for msg in msgs {
        match msg {
          MsgDown::Forget(_, _) => (),
          MsgDown::Invariants(sym, invs) => if self.sys == sym  {
            // event.log(
            //   & format!("received {} invariants", invs.len())
            // ) ;
            // event.log( & format!("add_invs [{}, {}]", check_offset, k) ) ;
            try_str!(
              base.add_invs(invs.clone()),
              "{} while adding invariants from supervisor to base at {}",
              err_pref, base.unroll_len()
            ) ;
            try_str!(
              step.add_invs(invs),
              "{} while adding invariants from supervisor to step at {}",
              err_pref, step.unroll_len()
            ) ;
          },
          _ => event.error("unknown message"),
        }
      },
    }
    Ok(())
  }

  /// `k`-splits some candidates using a step solver. Handles communication
  /// too.
  fn k_split<Base, Step>(
    & mut self, base: & mut Base, step: & mut Step, event: & mut Event
  ) -> Res<()> where
  Base: BaseTrait<Graph::Val, Step>,
  Step: StepTrait<Graph::Val, Base> {
    use term::{ STerm, STermSet, UnTermOps } ;

    let err_pref = "[Learner::k_split]" ;

    try_str!(
      self.recv(base, step, event),
      "{} before base stabilization", err_pref
    ) ;

    try_str!(
      self.graph.check(),
      "{} on input graph", err_pref
    ) ;

    let invars = try_str!(
      step.k_split(& mut self.candidates),
      "{} step query", err_pref
    ) ;

    if ! invars.is_empty() {
      let mut set = STermSet::with_capacity(invars.len()) ;
      for (invar, info) in invars.into_iter() {
        if let Some( (rep, to_drop) ) = info {
          try_str!(
            self.graph.drop_term(& rep, & to_drop),
            "{} while dropping `{}` from the class of `{}`",
            err_pref, to_drop, rep
          ) ;
        }
        let wasnt_there = self.known.insert(invar.clone()) ;
        debug_assert!(wasnt_there) ;
        let invar = try_str!(
          invar.to_term_safe(& self.factory),
          "{} while building one-state invariant", err_pref
        ) ;
        let wasnt_there = set.insert(
          STerm::One(
            try_str!(
              self.factory.debump(& invar),
              "{} while building one-state invariant", err_pref
            ),
            invar
          )
        ) ;
        debug_assert!( wasnt_there )
      } ;
      event.invariants_at( & self.sys, set, base.unroll_len() )
    }
    Ok(())
  }



  /// Stabilizes an equivalence class, extracts invariants. **Communicates
  /// invariants itself.** Returns `true` iff the graph is stable in base.
  ///
  /// # Pre-condition
  ///
  /// It should always be the case that
  ///
  /// ```
  /// base.unroll_len() + 1 >= step.unroll_len()
  /// ```
  fn stabilize_next_class<
    Base, Step,
    GetNext: Fn(& Self) -> Option<Term>,
    GraphLog: Fn(& Self, & str, & str) -> Res<()>
  >(
    & mut self, get_next: GetNext,
    base: & mut Base, step: & mut Step, event: & mut Event,
    graph_log: & GraphLog, tag: & str,
  ) -> Res< Option<Term> > where
  Base: BaseTrait<Graph::Val, Step>,
  Step: StepTrait<Graph::Val, Base> {

    let err_pref = "[Learner::stabilize_class]" ;

    debug_assert!(
      base.unroll_len() + 1 >= step.unroll_len()
    ) ;

    try_str!(
      self.graph.check(),
      "{} on input graph", err_pref
    ) ;

    try_str!(
      graph_log(& self, & tag, "0"),
      "{} could not dump graph as dot", err_pref
    ) ;

    let mut next = match get_next(self) {
      Some(next) => next,
      None => return Ok( None ),
    } ;

    // Stabilize the graph class by class until one is stable.
    'base_eq: loop {

      let to_check = if let Some(to_check) = try_str!(
        self.graph.base_cands_of_class(& next, & mut self.known),
        "{} while getting eq base terms of `{}`", err_pref, next
      ) {
        to_check
      } else {
        break 'base_eq
      } ;

      let eval_opt = try_str!(
        base.k_falsify(to_check),
        "{} during `k_falsify` query for eqs of `{}`", err_pref, next
      ) ;

      if let Some(mut eval) = eval_opt {
        // event.log("class is not stable, splitting") ;
        try!( self.graph.split(& mut eval) ) ;
        next = try_str_opt!(
          get_next(self),
          "{} graph was just split for eqs but no next rep found", err_pref
        )
      } else {
        // event.log("class is stable, moving on") ;
        break 'base_eq
      }

    }
    // At this point, `next` is the representative of a stable class with
    // stable parents.

    try_str!(
      self.recv(base, step, event),
      "{} before base stabilization", err_pref
    ) ;

    try_str!(
      graph_log(& self, & tag, "1"),
      "{} could not dump graph as dot", err_pref
    ) ;

    try_str!(
      self.graph.check(),
      "{} after eq stabilization", err_pref
    ) ;

    // Extract invariant from the equivalence class of `next`.
    self.candidates.clear() ;
    if self.early_eqs && try_str!(
      self.graph.step_cands_of_class(
        & next, & mut self.candidates, & mut self.known
      ),
      "{} while preparing `k_split` eq query over rep `{}`", err_pref, next
    ) {
      try_str!(
        self.k_split(base, step, event),
        "{} during `k_split` eq query over rep `{}`", err_pref, next
      )
    } ;
    Ok( Some(next) )
  }
}


impl<
  Graph: HasEdges + CanStabilize
> Learner<Graph> {
  /// Returns a representative for an unstable class.
  pub fn get_next(& self) -> Option<Term> {
    // Look for unstable rep with stable parents.
    'rep_loop: for (rep, parents) in self.graph.edges_bak().iter() {
      // Skip if stable.
      if self.stable.contains(rep) { continue 'rep_loop }
      // Inspect parents.
      'parent_loop: for parent in parents.iter() {
        // Skip the rep if parent's not stable.
        if ! self.stable.contains(parent) { continue 'rep_loop }
      }
      // Reachable only if all parents are stable.
      return Some( rep.clone() )
    }
    // Reachable only if no unstable rep has all its parents stable (graph is
    // stable).
    return None
  }

  /// Stabilizes an equivalence class, extracts invariants.
  /// **Communicates invariants itself.** Returns `true` iff the graph is
  /// stable in base.
  ///
  /// Once the class is stable, extracts invariants. Then, stabilizes all
  /// edges leading to this class, and extracts invariants once it's done.
  ///
  /// # TO DO
  ///
  /// Make `k_split`ting a loop so that it builds on the invariants it finds.
  pub fn stabilize_next_class_and_edges<
    Base, Step, GraphLog: Fn(& Self, & str, & str) -> Res<()>
  >(
    & mut self, base: & mut Base, step: & mut Step, event: & mut Event,
    graph_log: & GraphLog, tag: & str,
  ) -> Res< bool > where
  Base: BaseTrait<Graph::Val, Step>,
  Step: StepTrait<Graph::Val, Base> {

    let err_pref = "[Learner::stabilize_next_class_and_edges]" ;

    self.candidates.clear() ;

    let current = match try_str!(
      self.stabilize_next_class(
        |slf| slf.get_next(), base, step, event, graph_log, & tag
      ),
      "{} during class stabilization", err_pref
    ) {
      Some(current) => current,
      // Graph is stable.
      None => return Ok( true ),
    } ;

    'base_cmp: loop {

      let to_check = if let Some(to_check) = try_str!(
        self.graph.base_cands_of_edges(& current, & mut self.known),
        "{} while getting cmp base terms of `{}`", err_pref, current
      ) {
        to_check
      } else {
        break 'base_cmp
      } ;

      let eval_opt = try_str!(
        base.k_falsify(to_check),
        "{} during `k_falsify` query for cmps of `{}`", err_pref, current
      ) ;

      if let Some(mut eval) = eval_opt {
        try!( self.graph.split(& mut eval) )
      } else {
        break 'base_cmp
      }

    }
    // At this point, all edges leading to `next` are stable.

    try_str!(
      graph_log(& self, & tag, "0"),
      "{} could not dump graph as dot", err_pref
    ) ;

    try_str!(
      self.graph.check(),
      "{} after cmp stabilization", err_pref
    ) ;

    try_str!(
      self.recv(base, step, event),
      "{} before edge invariant extraction", err_pref
    ) ;

    // Extract invariant from the edges leading `current`.
    if self.early_cmps && try_str!(
      self.graph.step_cands_of_edges(
        & current, & mut self.candidates, & mut self.known
      ),
      "{} while preparing `k_split` cmp query over rep `{}`", err_pref, current
    ) {
      try_str!(
        self.k_split(base, step, event),
        "{} during `k_split` cmp query over rep `{}`", err_pref, current
      )
    } ;

    let wasnt_there = self.stable.insert(current) ;
    debug_assert!( wasnt_there ) ;

    try_str!(
      self.graph.check(),
      "{} after cmp invariant extraction", err_pref
    ) ;

    Ok(false)
  }

  /// Returns all the step terms for the graph. Equivalent to calling
  /// `step_terms_of_class` and `step_terms_of_edges` on all classes.
  fn step_cands(& mut self) -> Res<bool> {
    let err_pref = "[Learner::step_cands]" ;
    let mut new_stuff = false ;
    for (rep, _) in self.graph.classes() {
      new_stuff = new_stuff || try_str!(
        self.graph.step_cands_of_class(
          rep, & mut self.candidates, & self.known
        ),
        "{} on the class of rep `{}`", err_pref, rep
      ) ;
      new_stuff = new_stuff || try_str!(
        self.graph.step_cands_of_edges(
          rep, & mut self.candidates, & self.known
        ),
        "{} on the edges of rep `{}`", err_pref, rep
      )
    }
    Ok( new_stuff )
  }

  /// Looks for invariants in the whole graph.
  pub fn k_split_all<Base, Step>(
    & mut self, base: & mut Base, step: & mut Step, event: & mut Event
  ) -> Res<()> where
  Base: BaseTrait<Graph::Val, Step>,
  Step: StepTrait<Graph::Val, Base> {
    let err_pref = "[PartialGraph::k_split_all]" ;
    self.candidates.clear() ;
    let new_stuff = try_str!(
      self.step_cands(),
      "{} during step term extraction", err_pref
    ) ;
    if new_stuff {
      self.k_split(base, step, event)
    } else {
      Ok(())
    }
  }

}



/// Creates a graph-based learner.
pub fn mk_bool_learner(
  sys: Sys, factory: Factory, conf: & conf::Tig
) -> Learner< Graph<Bool> > {
  let (rep, class) = mine::bool(& factory, & sys, * conf.all_out()) ;
  Learner::mk(sys, rep, class, factory, conf)
}




/// The graph structure, storing the nodes and the edges.
pub struct Graph<Val: Domain> {
  /// Forward edges between representatives.
  map_for: TermMap<TermSet>,
  /// Backward edges between representatives.
  map_bak: TermMap<TermSet>,
  /// Maps representatives to their class.
  classes: TermMap<TermSet>,
  /// Remembers which classes have already been stabilized.
  /// Stores the representatives.
  memory: TermSet,
  /// Stores the representatives that have been split and their value.
  values: TermMap<Val>,
}

impl<Val: Domain> Graph<Val> {

  /// Creates an empty graph.
  #[inline]
  fn with_capacity(capa: usize) -> Self {
    Graph {
      map_for: TermMap::with_capacity( capa ),
      map_bak: TermMap::with_capacity( capa ),
      classes: TermMap::with_capacity( capa ),
      memory:  TermSet::with_capacity( capa ),
      values:  TermMap::with_capacity( capa ),
    }
  }

  /// Minimal set of candidate invariants the graph represents.
  pub fn candidates<
    Ignore: Fn(& TmpTerm) -> bool
  >(& self, ignore: Ignore) -> TmpTermSet {
    let mut set = TmpTermSet::with_capacity( self.classes.len() * 5 ) ;
    for (ref rep, ref class) in self.classes.iter() {
      for term in class.iter() {
        // println!("  {} = {}", rep, term) ;
        Val::insert_eq(rep, term, & mut set, & ignore)
      }
    }
    // println!("") ;
    for (ref rep, ref kids) in self.map_for.iter() {
      for kid in kids.iter() {
        Val::insert_cmp(rep, kid, & mut set, & ignore)
      }
    }
    set
  }

  /// All candidate invariants the graph represents.
  pub fn all_candidates<
    Ignore: Fn(& TmpTerm) -> bool
  >(& self, ignore: Ignore) -> Res<TmpTermSet> {
    let mut set = TmpTermSet::with_capacity( self.classes.len() * 5 ) ;
    for (ref rep, ref class) in self.classes.iter() {
      let mut class = class.iter() ;
      while let Some(term) = class.next() {
        // Equality with rep.
        Val::insert_eq(rep, term, & mut set, & ignore) ;
        // Equality with other terms.
        for other_term in class.clone() {
          Val::insert_eq(term, other_term, & mut set, & ignore)
        }
      }
    }
    for (ref rep, ref kids) in self.map_for.iter() {
      let class = try_str_opt!(
        self.classes.get(rep),
        "[Graph::all_candidates] could not retrieve class of rep {}", rep
      ) ;
      for kid in kids.iter() {
        let kid_class = try_str_opt!(
          self.classes.get(kid),
          "[Graph::all_candidates] could not retrieve class of rep {}", rep
        ) ;
        // Comparison rep/kid.
        Val::insert_cmp(rep, kid, & mut set, & ignore) ;
        // Comparison rep/kid_class.
        for kid in kid_class.iter() {
          Val::insert_cmp(rep, kid, & mut set, & ignore)
        }
        // Rest.
        for parent in class.iter() {
          Val::insert_cmp(parent, kid, & mut set, & ignore) ;
          for kid in kid_class.iter() {
            Val::insert_cmp(parent, kid, & mut set, & ignore)
          }
        }
      }
    }
    Ok(set)
  }

  /// Isolates a representative. Returns the old kids and parents of the rep.
  pub fn isolate(& mut self, rep: & Term) -> Res<(TermSet, TermSet)> {
    let err_pref = "[Graph::isolate]" ;
    let kids = if let Some( kids ) = self.map_for.remove(rep) {
      self.map_for.insert(rep.clone(), TermSet::new()) ;
      for kid in kids.iter() {
        if let Some( kid_parents ) = self.map_bak.get_mut(kid) {
          let was_there = kid_parents.remove(rep) ;
          debug_assert!( was_there )
        } else {
          error!(
            "{} unknown kid {} of rep {} in `map_bak`", err_pref, kid, rep
          )
        }
      }
      kids
    } else {
      error!(
        "{} unknown rep {} in `map_for`", err_pref, rep
      )
    } ;

    let parents = if let Some( parents ) = self.map_bak.remove(rep) {
      self.map_bak.insert(rep.clone(), TermSet::new()) ;
      for parent in parents.iter() {
        if let Some( parent_kids ) = self.map_for.get_mut(parent) {
          let was_there = parent_kids.remove(rep) ;
          debug_assert!( was_there )
        } else {
          error!(
            "{} unknown parent {} of rep {} in `map_for`",
            err_pref, parent, rep
          )
        }
      }
      parents
    } else {
      error!("{} unknown rep {} in `map_bak`", err_pref, rep)
    } ;

    Ok( (kids, parents) )
  }

  /// Adds a single kid to a representative.
  pub fn add_kid_ref(
    & mut self, rep: Term, kid: & Term
  ) -> () {
    // println!("      linking {} to {}", rep, kid) ;
    let to_insert = match self.map_bak.get_mut(kid) {
      // Add parent to parents.
      Some(set) => {
        let _ = set.insert(rep.clone()) ;
        None
      },
      // Add parent as new set.
      None => {
        let mut set = TermSet::new() ;
        set.insert(rep.clone()) ;
        Some(set)
      },
    } ;
    if let Some(to_insert) = to_insert {
      self.map_bak.insert(kid.clone(), to_insert) ;
    }

    // Add backward edge if `rep` is not in `map_bak`.
    if ! self.map_bak.contains_key(& rep) {
      self.map_bak.insert(rep.clone(), TermSet::new()) ;
      ()
    }

    // Update forward edges.
    let set = if let Some(mut set) = self.map_for.remove(& rep) {
      set.insert(kid.clone()) ;
      set
    } else {
      let mut set = TermSet::new() ;
      set.insert( kid.clone() ) ;
      set
    } ;
    // Add the new kids.
    self.map_for.insert(rep.clone(), set) ;

    ()
  }

  /// Adds kids to a representative. Updates `map_for` and `map_bak`.
  pub fn add_kids(
    & mut self, rep: & Term, kids: TermSet
  ) -> () {
    // Update backward edges.
    for kid in kids.iter() {
      match self.map_bak.get_mut(kid) {
        // Add parent to parents.
        Some(set) => {
          let _ = set.insert(rep.clone()) ;
          continue
        },
        // Add parent as new set.
        None => (),
      } ;
      let mut set = TermSet::new() ;
      set.insert(rep.clone()) ;
      let _ = self.map_bak.insert(kid.clone(), set) ;
      ()
    }

    // Add backward edge if `rep` is not in `map_bak`.
    if ! self.map_bak.contains_key(rep) {
      self.map_bak.insert(rep.clone(), TermSet::new()) ;
      ()
    }

    // Update forward edges.
    match self.map_for.remove(rep) {
      Some(mut set) => {
        for kid in kids.into_iter() {
          set.insert(kid) ;
        }
        // Add the new kids.
        self.map_for.insert(rep.clone(), set) ;
      },
      None => {
        self.map_for.insert(rep.clone(), kids) ;
        ()
      },
    }

    ()
  }

  /// Adds kids to a representative. Updates `map_for` and `map_bak`.
  ///
  /// Version where `kids` is a reference.
  pub fn add_kids_ref(
    & mut self, rep: & Term, kids: & TermSet
  ) -> Res<()> {
    // Update backward edges.
    for kid in kids.iter() {
      match self.map_bak.get_mut(kid) {
        // Add parent to parents.
        Some(set) => {
          let _ = set.insert(rep.clone()) ;
          continue
        },
        // Add parent as new set.
        None => (),
      } ;
      let mut set = TermSet::new() ;
      set.insert(rep.clone()) ;
      let _ = self.map_bak.insert(kid.clone(), set) ;
      ()
    }

    // Add backward edge if `rep` is not in `map_bak`.
    if ! self.map_bak.contains_key(rep) {
      self.map_bak.insert(rep.clone(), TermSet::new()) ;
      ()
    }

    // Update forward edges.
    match self.map_for.remove(rep) {
      Some(mut set) => {
        for kid in kids.iter() {
          set.insert(kid.clone()) ;
        }
        // Add the new kids.
        self.map_for.insert(rep.clone(), set) ;
      },
      None => error!("[Graph::add_kids] unknown rep {}", rep),
    }

    Ok(())
  }

  /// Length of `map_for`, `map_bak`, and `classes`.
  pub fn lens(& self) -> (usize, usize, usize) {
    (self.map_for.len(), self.map_bak.len(), self.classes.len())
  }

  /// Dumps a graph as dot to a file. Also runs dot to the generate the PDF.
  pub fn dot_dump(& self, path: & str) -> Res<()> {
    use std::fs::File ;
    use std::process::Command ;
    let err_pref = "[Graph::dot_dump]" ;
    let mut file = try_str!(
      File::create(path),
      "{} could not create file {}", err_pref, path
    ) ;
    try_str!(
      self.dot_fmt(& mut file),
      "{} could not dump graph as dot in file {}", err_pref, path
    ) ;
    let mut child = try_str!(
      Command::new("dot").arg("-Tpdf").arg("-o").arg(
        & format!("{}.pdf", path)
      ).arg(path).spawn(),
      "could not spawn `dot` command"
    ) ;
    let ecode = try_str!(
      child.wait(),
      "while running `dot` command"
    ) ;
    if ecode.success() {
      Ok(())
    } else {
      let mut err = format!("`dot` command failed:") ;
      if let Some( stderr ) = child.stderr {
        use std::io::{ BufReader, BufRead } ;
        let reader = BufReader::new(stderr) ;
        for line in reader.lines() {
          let line = try_str!(
            line,
            "{}\n[< {} could not retrieve line of stdout >]", err, err_pref
          ) ;
          err = format!("{}\n{}", err, line)
        }
        Err(err)
      } else {
        Err(
          format!(
            "{}\n[< {} could not retrieve stdout of process >]", err_pref, err
          )
        )
      }
    }
  }

  /// Formats a graph in dot format.
  pub fn dot_fmt<W: io::Write>(& self, w: & mut W) -> Res<()> {
    let err_pref = "[Graph::dot_fmt]" ;
    // Header.
    try_str!(
      write!(
        w,
        "\
digraph mode_graph {{
  graph [bgcolor=black margin=0.0] ;
  node [
    style=filled
    fillcolor=black
    fontcolor=\"#1e90ff\"
    color=\"#666666\"
  ] ;
  edge [color=\"#1e90ff\" fontcolor=\"#222222\"] ;

\
        "
      ), "{} while writing edge header", err_pref
    ) ;

    // Printing edges forward.
    for (rep, kids) in self.map_for.iter() {
      let size = match self.classes.get(rep) {
        Some(class) => class.len(),
        None => error!(
          "{} rep {} has no equivalence class", err_pref, rep
        )
      } ;
      let value = match self.values.get(rep) {
        Some(v) => format!("{}", v),
        None => format!("_"),
      } ;
      for kid in kids.iter() {
        let kid_size = match self.classes.get(kid) {
          Some(class) => class.len(),
          None => error!(
            "{} rep {} has no equivalence class", err_pref, kid
          )
        } ;
        let kid_value = match self.values.get(kid) {
          Some(v) => format!("{}", v),
          None => format!("_"),
        } ;
        try_str!(
          write!(
            w,
            "  \
              \"{} ({}, {})\" -> \"{} ({}, {})\" [\n    \
                constraint = false\n  \
              ] ;\n\
            ", rep, size, value, kid, kid_size, kid_value
          ), "{} while writing forward edge", err_pref
        )
      }
    } ;

    // Printing edges backward.
    for (rep, parents) in self.map_bak.iter() {
      let size = match self.classes.get(rep) {
        Some(class) => class.len(),
        None => error!(
          "{} rep {} has no equivalence class", err_pref, rep
        )
      } ;
      let value = match self.values.get(rep) {
        Some(v) => format!("{}", v),
        None => format!("_"),
      } ;
      for parent in parents.iter() {
        let parent_size = match self.classes.get(parent) {
          Some(class) => class.len(),
          None => error!(
            "{} rep {} has no equivalence class", err_pref, parent
          )
        } ;
        let parent_value = match self.values.get(parent) {
          Some(v) => format!("{}", v),
          None => format!("_"),
        } ;
        try_str!(
          write!(
            w,
            "  \
              \"{} ({}, {})\" -> \"{} ({}, {})\" [\n    \
                color = \"red\"\n  \
              ] ;\n\
            ", parent, parent_size, parent_value, rep, size, value
          ), "{} while writing backward edge", err_pref
        )
      }
    } ;
    try_str!(
      write!(
        w,
        "  \
  node [
    style=filled
    fillcolor=black
    fontcolor=\"#1e90ff\"
    color=\"#66FF66\"
  ] ;
  edge [color=\"#FF9090\" fontcolor=\"#222222\"] ;

\
        "
      ), "{} while writing class header", err_pref
    ) ;

    // Printing classes.
    for (rep, class) in self.classes.iter() {
      let rep_value = match self.values.get(rep) {
        Some(v) => format!("{}", v),
        None => format!("_"),
      } ;
      try_str!(
        write!(
          w,
          "  \
            \"{} ({})\" -> \"\
          ",
          rep, rep_value
        ), "{} while writing class arrow", err_pref
      ) ;
      let mut first = true ;
      for term in class.iter() {
        let pref = if first {
          first = false ;
          ""
        } else { "\\n" } ;
        try_str!(
          write!(w, "{}{}", pref, term),
          "{} while writing class arrow", err_pref
        )
      }
      try_str!(
        write!(w, "\" ;\n"),
        "{} while writing class arrow", err_pref
      )
    }

    Ok(
      try_str!(
        write!(w, "}}\n"),
        "{} during final newline", err_pref
      )
    )
  }

  /// Class corresponding to a representative.
  #[inline]
  pub fn class_of<'a, 'b>(
    & 'a self, rep: & 'b Term
  ) -> Result<& 'a TermSet, String> {
    match self.classes.get(rep) {
      Some(set) => Ok(set),
      None => error!(
        "[Graph::class_of] representative `{}` is unknown", rep
      ),
    }
  }

  /// Class corresponding to a representative (mutable version).
  #[inline]
  pub fn class_mut_of<'a, 'b>(
    & 'a mut self, rep: & 'b Term
  ) -> Result<& 'a mut TermSet, String> {
    match self.classes.get_mut(rep) {
      Some(set) => Ok(set),
      None => error!(
        "[Graph::class_mut_of] representative {} is unknown", rep
      ),
    }
  }

  /// Kids corresponding of a representative.
  #[inline]
  pub fn kids_of<'a, 'b>(
    & 'a self, rep: & 'b Term
  ) -> Result<& 'a TermSet, String> {
    match self.map_for.get(rep) {
      Some(set) => Ok(set),
      None => error!(
        "[Graph::kids_of] representative {} is unknown", rep
      ),
    }
  }

  /// Kids corresponding to a representative (mutable version).
  #[inline]
  pub fn kids_mut_of<'a, 'b>(
    & 'a mut self, rep: & 'b Term
  ) -> Result<& 'a mut TermSet, String> {
    match self.map_for.get_mut(rep) {
      Some(set) => Ok(set),
      None => error!(
        "[Graph::kids_mut_of] representative {} is unknown", rep
      ),
    }
  }

  /// Returns true iff all the parents of a rep are valued, except `term`.
  #[inline]
  pub fn has_valued_parents_except(
    & self, rep: & Term, term: & Term
  ) -> Result<bool, String> {
    match self.map_bak.get(rep) {
      Some(parents) => {
        for parent in parents.iter() {
          if parent != term && ! self.values.contains_key(parent) {
            return Ok(false)
          }
        }
        Ok(true)
      },
      None => error!(
        "[Graph::has_valued_parents] representative {} is unknown", rep
      ),
    }
  }

  /// Parents corresponding of a representative.
  #[inline]
  pub fn parents_of<'a, 'b>(
    & 'a self, rep: & 'b Term
  ) -> Result<& 'a TermSet, String> {
    match self.map_bak.get(rep) {
      Some(set) => Ok(set),
      None => error!(
        "[Graph::parents_of] representative {} is unknown", rep
      ),
    }
  }

  /// Parents corresponding to a representative (mutable version).
  #[inline]
  pub fn parents_mut_of<'a, 'b>(
    & 'a mut self, rep: & 'b Term
  ) -> Result<& 'a mut TermSet, String> {
    match self.map_bak.get_mut(rep) {
      Some(set) => Ok(set),
      None => error!(
        "[Graph::parents_mut_of] representative {} is unknown", rep
      ),
    }
  }

  /// Clears the stabilization memory. Call before starting a stabilization
  /// step.
  #[inline]
  pub fn clear_memory(& mut self) {
    self.memory.clear()
  }

  /// Removes a term from a class corresponding to a representative.
  pub fn drop_member(
    & mut self, rep: & Term, elem: & Term
  ) -> Res<bool> {
    // Getting the right equivalence class. */
    let class = try_str!(
      self.class_mut_of(rep),
      "[Graph::drop_member] retrieving class of {}", rep
    ) ;
    // Removing element.
    Ok( class.remove(elem) )
  }

  /// Splits a class corresponding to a representative, given an evaluator.
  ///
  /// Returns a chain.
  ///
  /// Only modifies the `classes` and `values` fields of the graph to break
  /// `rep`'s class and create the ones encoded in the final chain, and update
  /// the values of the different representatives.
  pub fn split_class(
    & mut self, rep: & Term, eval: & mut Eval<Val>
  ) -> Res< Chain<Val, ()> > {
    let err_pref = "[Graph::split_class]" ;
    // Starting with an empty chain.
    let mut chain = Chain::nil() ;
    
    {
      let class = match self.classes.get(rep) {
        Some(class) => class,
        None => error!("{} representative {} is unknown", err_pref, rep),
      } ;
      // Evaluate representative first.
      chain = try_str!(
        chain.insert(
          try_str!(
            eval.eval_term(rep),
            "{} while evaluating representative", err_pref
          ),
          rep.clone()
        ),
        "{} while inserting representative in the chain", err_pref
      ) ;
      // Evaluate everyone and insert as needed.
      for term in class.iter() {
        chain = try_str!(
          chain.insert(
            try_str!(
              eval.eval_term(term),
              "{} while evaluating term for rep {}", err_pref, rep
            ),
            term.clone()
          ),
          "{} while inserting in chain for rep {}", err_pref, rep
        ) ;
      }
    } ;

    // Update `classes` and `values`.
    let chain = chain.map_to_unit(
      |graph, v, rep, set| {
        // println!("    values.insert({}, {})", rep, v) ;
        let _ = graph.values.insert(rep.clone(), v) ;
        let _ = graph.classes.insert(rep, set) ;
        ()
      },
      self
    ) ;
    // Return the chain.
    Ok(chain)
  }

  /// Inserts a chain in a graph.
  pub fn insert_chain(
    & mut self, rep: & Term, chain: Chain<Val, ()>
  ) -> Res<()> {
    let err_pref = "[Graph::insert_chain]" ;
    if chain.is_empty() {
      error!("{} cannot insert an empty chain", err_pref)
    }

    let (kids, to_update) = try_str!(
      self.isolate(rep), "{} while link breaking", err_pref
    ) ;

    // Create links between elements of the chain.
    let _ = chain.fold(
      (& mut * self, None),
      |(mut graph, prev), _, rep, _| {
        if let Some(prev) = prev {
          graph.add_kid_ref((* rep).clone(), & prev)
        } else {
          graph.add_kids(rep, TermSet::new() )
        }
        (graph, Some(rep.clone()))
      }
    ) ;

    let last_of_chain = chain.last().unwrap().1.clone() ;

    let mut stack = vec![ (chain, kids, to_update) ] ;

    // Inserting in the parents.
    loop {

      match stack.pop() {

        // No chain to insert. Link the reps to update to the kids above.
        Some( (Chain::Nil, kids, set) ) => {
          // println!("  - chain: []") ;
          // println!("    kids:  {:?}", kids) ;
          // println!("    set:   {:?}", set) ;
          for parent in set.into_iter() {
            try_str!(
              self.add_kids_ref(& parent, & kids),
              "{} while linking on an empty chain", err_pref
            )
          }
        },

        Some( (chain, kids, mut set) ) => {
          // println!("  - chain: {}", chain) ;
          // println!("    kids:  {:?}", kids) ;
          // println!("    set:   {:?}", set) ;
          // Chain is not empty. Anything in the set?
          let parent = set.iter().next().map(|parent| parent.clone()) ;

          // `unwrap`-s can't fail here, chain's not empty.
          let (top_value, top_rep) = chain.top_value().unwrap() ;

          if let Some(parent) = parent {
            // println!("    parent: {}", parent) ;
            // Removing parent and pushing the set back on the stack.
            set.remove(& parent) ;
            stack.push( (chain.clone(), kids.clone(), set.clone()) ) ;
            // Retrieving the value of the parent.
            let parent_value = match self.values.get(& parent) {
              Some(v) => v.clone(),
              None => error!("{} parent {} has no value", err_pref, parent),
            } ;

            // Can we insert anything above this parent?
            if parent_value <= top_value {
              // println!("    parent value above top value") ;
              // Link kids to top rep.
              self.add_kids(& top_rep, kids) ;
              // Longest chain to insert above this parent.
              let (above, chain) = chain.split_at(& parent_value) ;
              // println!("    above: {:?}", above) ;
              debug_assert!( above.len() > 0 ) ;

              let mut kids = TermSet::new() ;
              // Can't fail, `chain` can't be empty.
              kids.insert( above[0].clone() ) ;
              // Link parent to last rep of the chain.
              // println!("    parent to last rep") ;
              self.add_kid_ref( parent.clone(), & above[0] ) ;
              // Iterate on the rest of the chain if it's not empty.
              if ! chain.is_empty() {
                // println!("    chain below is not empty") ;
                stack.push((
                  chain,
                  kids,
                  try_str!(
                    self.parents_of(& parent),
                    "{} while retrieving parents of parent {} (1)",
                    err_pref, parent
                  ).clone()
                ))
              } else {
                // println!("    chain below is empty") ;
                self.add_kid_ref(parent, & last_of_chain)
              }

            } else {
              // println!("    parent value below top value") ;
              // Nothing to insert above. Link kids to parent and to top.
              try_str!(
                self.add_kids_ref(& parent, & kids),
                "{} while adding kids to parent {} (2)", err_pref, parent
              ) ;
              self.add_kids(& top_rep, kids) ;
              stack.push(
                (
                  chain,
                  TermSet::new(),
                  try_str!(
                    self.parents_of(& parent),
                    "{} while retrieving parents of parent {} (2)",
                    err_pref, parent
                  ).clone()
                )
              )
            }

          } else {
            // println!("    no parent") ;
            self.add_kids(& top_rep, kids) ;
            // Nothing left to update, move on to the rest of the stack.
            ()
          }
        },

        None => break,
      }

    }

    Ok(())
  }

  /// Orphan representatives in the graph.
  pub fn orphans(& self) -> TermSet {
    let mut orphans = TermSet::with_capacity(self.classes.len() / 2) ;
    for (rep, parents) in self.map_bak.iter() {
      if parents.is_empty() {
        let wasnt_there = orphans.insert( rep.clone() ) ;
        debug_assert!( wasnt_there )
      }
    }
    orphans
  }

}

impl< Val: Domain > CanLog for Graph<Val> {
  fn log_to(& self, path: & str) -> Res<()> {
    self.dot_dump(path)
  }
}

impl< Val: Domain > CanStabilize for Graph<Val> {
  type Val = Val ;

  fn split(& mut self, eval: & mut Eval<Val>) -> Res<()> {
    // INVARIANT: a class can be split **iff** all its parents have already
    //            been split.
    // This is forced by starting from orphan nodes in the graph, splitting
    // them, and then iterating on their kids.
    let err_pref = "[Graph::split]" ;

    // Clear `values` memory.
    self.values.clear() ;

    // Get all orphan representatives.
    let mut to_do = self.orphans() ;

    // Stabilization loop.
    'to_do: loop {

      // If there's something in `to_do`, work on that. Otherwise `break`.
      let rep = match to_do.iter().next() {
        Some(next) => next.clone(),
        None => break 'to_do
      } ;

      // Add kids of `rep` to `to_do`.
      {
        let kids = try_str!(
          self.kids_of(& rep),
          "{} while retrieving the kids of rep {}", err_pref, rep
        ) ;
        for kid in kids.iter() {
          if try_str!(
            self.has_valued_parents_except(kid, & rep),
            "{} while checking if kid {} has valued parents", err_pref, kid
          ) {
            to_do.insert(kid.clone()) ;
            ()
          }
        }
      }

      // Remove `rep` from to_do as we're gonna handle it.
      to_do.remove(& rep) ;

      // Split equivalence class.
      let chain = try_str!(
        self.split_class(& rep, eval),
        "{} while splitting rep {}", err_pref, rep
      ) ;
      // Insert resulting chain.
      try_str!(
        self.insert_chain(& rep, chain),
        "{} while inserting chain after splitting rep {}", err_pref, rep
      ) ;

    }

    Ok(())
  }
}

impl< Val: Domain > HasClasses for Graph<Val> {
  fn mk(rep: Term, class: TermSet) -> Self {
    // Creating empty graph.
    let mut graph = Graph::with_capacity(class.len() / 3) ;
    // `rep` has no kids.
    graph.map_for.insert(
      rep.clone(), TermSet::with_capacity(class.len() / 10)
    ) ;
    // `rep` has no parents.
    graph.map_bak.insert(
      rep.clone(), TermSet::with_capacity(class.len() / 10)
    ) ;
    // `rep`'s class is the one provided.
    graph.classes.insert(rep, class) ;
    // Done.
    graph
  }
  fn classes(& self) -> & Classes { & self.classes }
  fn mut_classes(& mut self) -> & mut Classes { & mut self.classes }
}

impl< Val: Domain > HasEdges for Graph<Val> {
  fn edges_for(& self) -> & Classes { & self.map_for }
  fn mut_edges_for(& mut self) -> & mut Classes { & mut self.map_for }
  fn edges_bak(& self) -> & Classes { & self.map_bak }
  fn mut_edges_bak(& mut self) -> & mut Classes { & mut self.map_bak }
}