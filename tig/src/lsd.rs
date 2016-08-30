// Copyright 2016 Adrien Champion. See the COPYRIGHT file at the top-level
// directory of this distribution.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

/*! Lock Step Driver (LSD): a wrapper around some SMT solvers providing
invariant-generation-oriented operations. */

use std::collections::{ HashSet, HashMap } ;

use common::Res ;

use term::tmp::TmpTerm as Term ;

use Domain ;
use eval::Eval ;

/// A set of temp terms with some info.
pub type TermMap<Info> = HashMap<Term, Info> ;
/// A set of temp terms.
pub type TermSet = HashSet<Term> ;

/// Wrapper to perform checks on a trace of reachable states.
pub trait BaseTrait<
  Val: Domain, S: StepTrait<Val, Self>
>: Lsd<Val, Self, S> where Self: Sized {
  /// Returns a model for the last state of a trace of k (current unrolling)
  /// states falsifying at least one of the terms from the list at k.
  fn k_falsify(
    & mut self, Vec<Term>
  ) -> Res<Option<& mut Eval<Val>>> ;
}

/// Wrapper to perform checks on a trace of states.
pub trait StepTrait<
  Val: Domain, B: BaseTrait<Val, Self>
>: Lsd<Val, B, Self> where Self: Sized {
  /// Splits the input set in two: the terms unfalsifiable terms in a
  /// k-induction check for the current depth, and the rest.
  fn k_split<Info>(
    & mut self, TermMap<Info>
  ) -> Res<(TermMap<Info>, TermMap<Info>)> ;
}

/// High-level LSD features.
pub trait Lsd<
  Val: Domain, B: BaseTrait<Val, S>, S: StepTrait<Val, B>
> {
  /// Restarts the lsd engine. The unrollings are restored.
  fn restart(& mut self) -> Res<()> ;
  /// Turns an lsd into its base version.
  fn to_base(self) -> Res<B> ;
  /// Turns an lsd into its step version.
  fn to_step(self) -> Res<S> ;
  /// Number of unrollings.
  fn unroll_len(& self) -> usize ;
  /// Unrolls one transition further. Returns the new depth.
  fn unroll(& mut self) -> Res<usize> ;
}


/// Top only lsd.
///
/// - only supports one system
/// - restarts solver when base/step switching
pub mod top_only {

  use common::{ SolverTrait, Res } ;
  use term::{ Offset2, Bool } ;
  use term::tmp::TmpTerm as Term ;
  use term::tmp::TmpTermMker ;
  use system::Sys ;
  use unroll::{ Unroller, ActlitFactory } ;

  use Domain ;
  use eval::Eval ;
  pub use lsd::{
    BaseTrait, StepTrait, Lsd
  } ;

  pub use super::{ TermSet, TermMap } ;

  /// Base checker.
  pub struct Base<Val: Domain, Solver> {
    /// The system this checker corresponds to.
    sys: Sys,
    /// The solver process.
    solver: Solver,
    /// The current unrolling depth.
    k: Offset2,
    /// Actlit factory.
    actlit: ActlitFactory,
    /// Cached evaluator.
    eval: Eval<Val>,
  }
  impl<
    'a, Val: Domain, Solver: SolverTrait<'a>
  > Base<Val, Solver> {
    /// Base setup for a solver.
    fn setup(sys: & Sys, solver: & mut Solver, unroll: usize) -> Res<Offset2> {
      let mut k = Offset2::init() ;
      try_str!(
        solver.reset(),
        "while `reset`ing the solver"
      ) ;
      try_str!(
        sys.defclare_funs(solver),
        "while declaring UFs, init and trans"
      ) ;
      try_str!(
        sys.assert_init(solver, & k),
        "while asserting init"
      ) ;
      // Init is asserted, we need to decrease `k` so that it accounts
      // for the fact that there is `0` unrolling.
      k = k.pre() ;
      for _ in 0..unroll {
        k = k.nxt() ;
        try_str!(
          sys.unroll(solver, & k),
          "while unrolling system at {}", k.next()
        )
      }
      Ok(k)
    }
    /// Creates a base checker. Unrolls the transition relation `unroll` times.
    fn of(
      sys: Sys, mut solver: Solver, unroll: usize, eval: Eval<Val>
    ) -> Res<Self> {
      Base::<Val, Solver>::setup(& sys, & mut solver, unroll).map(
        |k| Base {
          sys: sys, solver: solver, k: k,
          actlit: ActlitFactory::mk(),
          eval: eval
        }
      )
    }

    /// Creates a base checker, unrolls the transition relation `unroll` times.
    pub fn mk(sys: Sys, solver: Solver, unroll: usize) -> Res<Self> {
      let factory = solver.parser().clone() ;
      Base::of(
        sys, solver, unroll, Eval::mk(
          vec![], Step::<Val, Solver>::check_offset(), factory
        )
      )
    }

    /// Creates a base checker from a step checker, with the same unrolling.
    #[inline]
    pub fn of_step(step: Step<Val, Solver>) -> Res<Self> {
      Self::of(step.sys, step.solver, step.k.next().to_usize(), step.eval)
    }
  }

  impl<
    'a, Val: Domain, Solver: SolverTrait<'a>
  > BaseTrait< Val, Step<Val, Solver> > for Base<Val, Solver> {
    fn k_falsify(
      & mut self, terms: Vec<Term>
    ) -> Res< Option< & mut Eval<Val> > > {
      // Creating the term to check.
      let one_term_false = Term::and(terms).tmp_neg() ;
      // Creating actlit for this check.
      let actlit = self.actlit.mk_fresh() ;
      actlit.declare(& mut self.solver).expect(
        & format!(
          "while declaring activation literal at {}", self.k
        )
      ) ;
      let implication = actlit.activate_term(one_term_false) ;

      try_str!(
        self.solver.assert(& implication, & self.k),
        "while asserting implication at {}", self.k
      ) ;

      // Check sat.
      let is_sat = try_str!(
        self.solver.check_sat_assuming( & [ actlit.name() ], & () ),
        "during a `check_sat_assuming` query at {}", self.k
      ) ;

      let res = if is_sat {
        // Sat, getting model.
        let model = try_str!(
          self.solver.get_model(),
          "could not retrieve model"
        ) ;
        self.eval.recycle( model, self.k.clone() ) ;
        Some(& mut self.eval)
      } else {
        // Unsat.
        None
      } ;
      
      try_str!(
        actlit.deactivate(& mut self.solver),
        "could not deactivate negative actlit"
      ) ;

      Ok(res)
    }
  }

  impl<
    'a, Val: Domain, Solver: SolverTrait<'a>
  > Lsd< Val, Base<Val, Solver>, Step<Val, Solver> > for Base<Val, Solver> {
    fn restart(& mut self) -> Res<()> {
      match Base::<Val, Solver>::setup(
        & self.sys, & mut self.solver, self.k.next().to_usize()
      ) {
        Ok(k) => {
          debug_assert!(k == self.k) ;
          Ok(())
        },
        Err(e) => Err(e),
      }
    }
    fn to_base(self) -> Res< Base<Val, Solver> > {
      Ok(self)
    }
    fn to_step(self) -> Res< Step<Val, Solver> > {
      Step::of_base(self)
    }
    fn unroll_len(& self) -> usize {
      self.k.next().to_usize()
    }
    fn unroll(& mut self) -> Res<usize> {
      self.k = self.k.nxt() ;
      try_str!(
        self.sys.unroll(& mut self.solver, & self.k),
        "while unrolling system at {}", self.k.next()
      ) ;
      Ok( self.unroll_len() )
    }
  }











  /// Step checker.
  pub struct Step<Val: Domain, Solver> {
    /// The system this checker corresponds to.
    sys: Sys,
    /// The solver process.
    solver: Solver,
    /// The current unrolling depth.
    k: Offset2,
    /// The offset corresponding to the checks. (Unrolling backwards.)
    check: Offset2,
    /// Actlit factory.
    actlit: ActlitFactory,
    /// Cached evaluator.
    eval: Eval<Val>,
  }
  impl<'a, Val: Domain, Solver: SolverTrait<'a>> Step<Val, Solver> {
    /// The offset used by the step solver for its checks.
    #[inline]
    fn check_offset() -> Offset2 { Offset2::init().rev() }
    /// Step setup for a solver.
    ///
    /// Returns the check offset and the unrolling offset.
    fn setup(
      sys: & Sys, solver: & mut Solver, unroll: usize
    ) -> Res<(Offset2, Offset2)> {
      if unroll < 1 {
        return Err(
          "illegal number of unrolling: 0\nmust be > 0".to_string()
        )
      }
      let check_offset = Step::<Val, Solver>::check_offset() ;
      let mut k = check_offset.clone() ;
      try_str!(
        solver.reset(),
        "while `reset`ing the solver"
      ) ;
      try_str!(
        sys.defclare_funs(solver),
        "while declaring UFs, init and trans"
      ) ;
      try_str!(
        sys.declare_svars(solver, check_offset.next()),
        // Unrolling backwards ~~~~~~~~~~~~~~~~~~~~~~^^^^
        "while declaring state variables"
      ) ;
      // First unrolling, to be consistent with the value of `k`.
      try_str!(
        sys.unroll(solver, & k),
        "while unrolling system at {}", k.next()
      ) ;
      // Unrolling loop, `unroll - 1` iterations because of the previous
      // unrolling. Hence `1..unroll` and not `0..unroll`.
      for _ in 1..unroll {
        k = k.nxt() ;
        try_str!(
          sys.unroll(solver, & k),
          "while unrolling system at {}", k.next()
        )
      }
      Ok( (check_offset, k) )
    }
    /// Creates a base checker, unrolls the system `unroll` times.
    /// `k = 0` is illegal and results in an error.
    fn of(
      sys: Sys, mut solver: Solver, unroll: usize, eval: Eval<Val>
    ) -> Res<Self> {
      Step::<Val, Solver>::setup(& sys, & mut solver, unroll).map(
        | (check, k) | Step {
          sys: sys, solver: solver, k: k, check: check.clone(),
          actlit: ActlitFactory::mk(), eval: eval
        }
      )
    }

    /// Creates a step checker from a base checker with the same number
    /// of unrollings.
    #[inline]
    pub fn of_base(base: Base<Val, Solver>) -> Res<Self> {
      Self::of(base.sys, base.solver, base.k.next().to_usize(), base.eval)
    }
  }

  impl<
    'a, Val: Domain, Solver: SolverTrait<'a>
  > StepTrait< Val, Base<Val, Solver> > for Step<Val, Solver> {
    fn k_split<Info>(
      & mut self, in_map: TermMap<Info>
    ) -> Res<(TermMap<Info>, TermMap<Info>)> {
      let len = in_map.len() ;
      let tenth_of_len = 1 + len / 10 ;
      let mut rest = TermMap::with_capacity( len - tenth_of_len ) ;

      // Creating one actlit per term to maximize solver learning.
      let mut map = TermMap::with_capacity(len) ;
      let mut positive = Vec::with_capacity(len) ;
      for (term, info) in in_map.into_iter() {
        let actlit = self.actlit.mk_fresh() ;
        actlit.declare(& mut self.solver).expect(
          & format!(
            "while declaring activation literal at {}", self.k
          )
        ) ;
        positive.push( actlit.activate_term( term.clone() ) ) ;
        let prev = map.insert(term, (info, actlit.name())) ;
        debug_assert!( prev.is_none() )
      }

      // Asserting all positive implications.
      let positive = Term::and(positive) ;
      let mut unroll = self.check.nxt() ;

      while unroll <= self.k {
        unroll = unroll.nxt() ;
        try_str!(
          self.solver.assert(& positive, & unroll),
          "while asserting positive implications at {}", unroll
        )
      }

      // Splitting loop.
      'split: loop {

        // Terms to check at this iteration.
        let mut to_check = Vec::with_capacity( map.len() ) ;
        // `+ 1` because we'll push the negative actlit.
        let mut actlits = Vec::with_capacity(map.len() + 1) ;
        for ( ref term, & (_, ref actlit) ) in map.iter() {
          // Yes, we're cloning each time...
          // Temp terms are supposed to be shallow though, so it should be
          // okay.
          to_check.push( (* term).clone() ) ;
          actlits.push( (* actlit).clone() )
        }
        let one_term_false = Term::and( to_check.clone() ).tmp_neg() ;

        // Creating actlit for this check.
        let actlit = self.actlit.mk_fresh() ;
        actlits.push( actlit.name() ) ;
        actlit.declare(& mut self.solver).expect(
          & format!(
            "while declaring activation literal at {}", self.k
          )
        ) ;
        let implication = actlit.activate_term(one_term_false) ;

        try_str!(
          self.solver.assert(& implication, & self.check),
          "while asserting implication at {}", self.k
        ) ;

        // Check sat.
        let is_sat = try_str!(
          self.solver.check_sat_assuming( & actlits, & () ),
          "during a `check_sat_assuming` query at {}", self.k
        ) ;

        if is_sat {
          use unroll::SysModel ;
          // Evaluate terms and update `rest`.
          let model = try_str!(
            self.sys.get_model( & mut self.solver, & self.check),
            "while retrieving the values of the candidate terms"
          ) ;
          
          let mut eval = Eval::<Bool>::mk(
            model,
            Step::<Val, Solver>::check_offset(),
            self.solver.parser().clone()
          ) ;

          for term in to_check.into_iter() {
            let term_is_true = try_str!(
              eval.eval(& term),
              "could not evaluate term {:?} in current model", term
            ) ;
            if ! term_is_true {
              // Falsified, remove from `map` and put in `rest`.
              match map.remove(& term) {
                Some( (info, _) ) => {
                  let pre = rest.insert(term, info) ;
                  debug_assert!( pre.is_none() )
                },
                None => return Err(
                  format!("unknown term {:?} in `to_check`", term)
                ),
              }
            }
          }
        }

        try_str!(
          actlit.deactivate(& mut self.solver),
          "could not deactivate negative actlit"
        ) ;

        // If we got unsat then we're done.
        if ! is_sat { break 'split }
      }
      debug_assert!( map.len() + rest.len() == len ) ;

      map.shrink_to_fit() ;
      let map = map.into_iter().map(
        | ( term, (info, _) )| (term, info)
      ).collect() ;
      rest.shrink_to_fit() ;
      Ok( (map, rest) )
    }
  }

  impl<
    'a, Val: Domain, Solver: SolverTrait<'a>
  > Lsd< Val, Base<Val, Solver>, Step<Val, Solver> > for Step<Val, Solver> {
    fn restart(& mut self) -> Res<()> {
      match Step::<Val, Solver>::setup(
        & self.sys, & mut self.solver, self.k.next().to_usize()
      ) {
        Ok( (check, k) ) => {
          debug_assert!(k == self.k) ;
          debug_assert!(check == self.check) ;
          Ok(())
        },
        Err(e) => Err(e),
      }
    }
    fn to_base(self) -> Res< Base<Val, Solver> > {
      Base::of_step(self)
    }
    fn to_step(self) -> Res< Step<Val, Solver> > {
      Ok(self)
    }
    fn unroll_len(& self) -> usize {
      self.k.next().to_usize()
    }
    fn unroll(& mut self) -> Res<usize> {
      self.k = self.k.nxt() ;
      try_str!(
        self.sys.unroll(& mut self.solver, & self.k),
        "while unrolling system at {}", self.k.next()
      ) ;
      Ok( self.unroll_len() )
    }
  }
}