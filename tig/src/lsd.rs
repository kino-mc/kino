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

use common::Res ;

use term::STermSet ;
use term::tmp::{ TmpTerm, TmpTermMap } ;

use Domain ;
use eval::Eval ;

/// Wrapper to perform checks on a trace of reachable states.
pub trait BaseTrait<
  Val: Domain, S: StepTrait<Val, Self>
>: Lsd<Val, Self, S> where Self: Sized {
  /// Returns a model for the last state of a trace of k (current unrolling)
  /// states falsifying at least one of the terms from the list at k.
  fn k_falsify(
    & mut self, Vec<TmpTerm>
  ) -> Res<Option<& mut Eval<Val>>> ;
}

/// Wrapper to perform checks on a trace of states.
pub trait StepTrait<
  Val: Domain, B: BaseTrait<Val, Self>
>: Lsd<Val, B, Self> where Self: Sized {
  /// Splits the input set in two: the terms unfalsifiable terms in a
  /// k-induction check for the current depth, and the rest.
  fn k_split<Info>(
    & mut self, TmpTermMap<Info>
  ) -> Res<(TmpTermMap<Info>, TmpTermMap<Info>)> ;
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
  /// Adds invariants to an lsd instance.
  fn add_invs(& mut self, STermSet) -> Res<()> ;
}


/// Top only lsd.
///
/// - only supports one system
/// - restarts solver when base/step switching
pub mod top_only {

  use common::{ SolverTrait, Res } ;
  use term::{ Offset2, Bool, STermSet } ;
  use term::tmp::TmpTerm as Term ;
  use term::tmp::{ TmpTermMker, TmpTermMap } ;
  use system::Sys ;
  use unroll::Unroller ;

  use Domain ;
  use eval::Eval ;
  pub use lsd::{
    BaseTrait, StepTrait, Lsd
  } ;

  /// Base checker.
  pub struct Base<Val: Domain, Solver> {
    /// The underlying unroller.
    unroller: Unroller<Solver>,
    /// The current unrolling depth.
    k: Offset2,
    /// Cached evaluator.
    eval: Eval<Val>,
  }
  impl<
    'a, Val: Domain, Solver: SolverTrait<'a>
  > Base<Val, Solver> {
    /// Base setup for a solver.
    fn setup(
      unroller: & mut Unroller<Solver>, unroll: usize
    ) -> Res<Offset2> {
      let mut k = Offset2::init() ;
      try_str!(
        unroller.solver().reset(),
        "while `reset`ing the solver {}", k
      ) ;
      try_str!(
        unroller.defclare_funs(& []),
        "while declaring UFs, init and trans"
      ) ;
      try_str!(
        unroller.assert_init(& k),
        "while asserting init"
      ) ;
      // Init is asserted, we need to decrease `k` so that it accounts
      // for the fact that there is `0` unrolling.
      k = k.pre() ;
      for _ in 0..unroll {
        k = k.nxt() ;
        try_str!(
          unroller.unroll(& k),
          "while unrolling system at {}", k.next()
        )
      }
      Ok(k)
    }
    /// Creates a base checker. Unrolls the transition relation `unroll` times.
    fn of(
      mut unroller: Unroller<Solver>, unroll: usize, eval: Eval<Val>
    ) -> Res<Self> {
      Base::<Val, Solver>::setup(& mut unroller, unroll).map(
        |k| Base {
          unroller: unroller, k: k, eval: eval
        }
      )
    }

    /// Creates a base checker, unrolls the transition relation `unroll` times.
    pub fn mk(sys: & Sys, solver: Solver, unroll: usize) -> Res<Self> {
      let factory = solver.parser().clone() ;
      let unroller = try_str!(
        Unroller::mk(sys, & [], solver), "while creating unroller"
      ) ;
      Base::of(
        unroller, unroll, Eval::mk(
          sys.clone(), vec![], Step::<Val, Solver>::check_offset(), factory
        )
      )
    }

    /// Creates a base checker from a step checker, with the same unrolling.
    #[inline]
    pub fn of_step(step: Step<Val, Solver>) -> Res<Self> {
      Self::of(step.unroller, step.k.next().to_usize(), step.eval)
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
      let actlit = try_str!(
        self.unroller.fresh_actlit(),
        "while declaring activation literal at {}", self.k
      ) ;
      let implication = actlit.activate_term(one_term_false) ;

      try_str!(
        self.unroller.assert(& implication, & self.k),
        "[Base::k_falsify] while asserting implication at {}", self.k
      ) ;

      // Check sat.
      let is_sat = try_str!(
        self.unroller.check_sat_assuming( & [ actlit.name() ] ),
        "[Base::k_falsify] during a `check_sat_assuming` query at {}", self.k
      ) ;

      let res = if is_sat {
        // Sat, getting model.
        let model = try_str!(
          self.unroller.solver().get_model(),
          "[Base::k_falsify] could not retrieve model"
        ) ;
        self.eval.recycle( model, self.k.clone() ) ;
        Some(& mut self.eval)
      } else {
        // Unsat.
        None
      } ;
      
      try_str!(
        self.unroller.deactivate(actlit),
        "[Base::k_falsify] could not deactivate negative actlit"
      ) ;

      Ok(res)
    }
  }

  impl<
    'a, Val: Domain, Solver: SolverTrait<'a>
  > Lsd< Val, Base<Val, Solver>, Step<Val, Solver> > for Base<Val, Solver> {
    fn restart(& mut self) -> Res<()> {
      match Base::<Val, Solver>::setup(
        & mut self.unroller, self.k.next().to_usize()
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
        self.unroller.unroll(& self.k),
        "while unrolling system at {}", self.k.next()
      ) ;
      Ok( self.unroll_len() )
    }
    fn add_invs(& mut self, invs: STermSet) -> Res<()> {
      self.unroller.add_invs(invs, & Offset2::init(), & self.k)
    }
  }











  /// Step checker.
  pub struct Step<Val: Domain, Solver> {
    /// The underlying unroller.
    unroller: Unroller<Solver>,
    /// The current unrolling depth.
    k: Offset2,
    /// The offset corresponding to the checks. (Unrolling backwards.)
    check: Offset2,
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
      unroller: & mut Unroller<Solver>, unroll: usize
    ) -> Res<(Offset2, Offset2)> {
      if unroll < 1 {
        return Err(
          "illegal number of unrolling: 0\nmust be > 0".to_string()
        )
      }
      let check_offset = Step::<Val, Solver>::check_offset() ;
      let mut k = check_offset.clone() ;
      try_str!(
        unroller.solver().reset(),
        "while `reset`ing the solver"
      ) ;
      try_str!(
        unroller.defclare_funs(& []),
        "while declaring UFs, init and trans"
      ) ;
      try_str!(
        unroller.declare_svars(check_offset.next()),
        // Unrolling backwards ~~~~~~~~~~~~~~~~~~~~~~^^^^
        "while declaring state variables"
      ) ;
      // First unrolling, to be consistent with the value of `k`.
      try_str!(
        unroller.unroll(& k),
        "while unrolling system at {}", k.next()
      ) ;
      // Unrolling loop, `unroll - 1` iterations because of the previous
      // unrolling. Hence `1..unroll` and not `0..unroll`.
      for _ in 1..unroll {
        k = k.nxt() ;
        try_str!(
          unroller.unroll(& k),
          "while unrolling system at {}", k.next()
        )
      }
      Ok( (check_offset, k) )
    }
    /// Creates a base checker, unrolls the system `unroll` times.
    /// `k = 0` is illegal and results in an error.
    fn of(
      mut unroller: Unroller<Solver>, unroll: usize, eval: Eval<Val>
    ) -> Res<Self> {
      Step::<Val, Solver>::setup(& mut unroller, unroll).map(
        | (check, k) | Step {
          unroller: unroller, k: k, check: check.clone(), eval: eval
        }
      )
    }

    /// Creates a step checker from a base checker with the same number
    /// of unrollings.
    #[inline]
    pub fn of_base(base: Base<Val, Solver>) -> Res<Self> {
      Self::of(base.unroller, base.k.next().to_usize(), base.eval)
    }
  }

  impl<
    'a, Val: Domain, Solver: SolverTrait<'a>
  > StepTrait< Val, Base<Val, Solver> > for Step<Val, Solver> {
    fn k_split<Info>(
      & mut self, in_map: TmpTermMap<Info>
    ) -> Res<(TmpTermMap<Info>, TmpTermMap<Info>)> {
      if in_map.is_empty() {
        return Ok(( TmpTermMap::new(), TmpTermMap::new() ))
      }

      let len = in_map.len() ;
      let tenth_of_len = 1 + len / 10 ;
      let mut rest = TmpTermMap::with_capacity( len - tenth_of_len ) ;

      // Creating one actlit per term to maximize solver learning.
      let mut map = TmpTermMap::with_capacity(len) ;
      let mut positive = Vec::with_capacity(len) ;
      for (term, info) in in_map.into_iter() {
        let actlit = try_str!(
          self.unroller.fresh_actlit(),
          "[Step::k_split] while declaring activation literal at {}", self.k
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
          self.unroller.assert(& positive, & unroll),
          "[Step::k_split] while asserting positive implications at {}", unroll
        )
      }

      // Splitting loop.
      'split: while ! map.is_empty() {

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
        let actlit = try_str!(
          self.unroller.fresh_actlit(),
          "[Step::k_split] while declaring activation literal at {}", self.k
        ) ;
        actlits.push( actlit.name() ) ;
        let implication = actlit.activate_term(one_term_false) ;

        try_str!(
          self.unroller.assert(& implication, & self.check),
          "[Step::k_split] while asserting implication for {} terms at {}",
          to_check.len(), self.k
        ) ;

        // Check sat.
        let is_sat = try_str!(
          self.unroller.check_sat_assuming( & actlits ),
          "[Step::k_split] during a `check_sat_assuming` query at {}", self.k
        ) ;

        if is_sat {
          // Evaluate terms and update `rest`.
          let model = try_str!(
            self.unroller.get_model(& self.check),
            "[Step::k_split] while retrieving the values of the candidate terms"
          ) ;
          
          let mut eval = Eval::<Bool>::mk(
            self.unroller.sys().clone(), model,
            Step::<Val, Solver>::check_offset(),
            self.unroller.solver().parser().clone()
          ) ;

          for term in to_check.into_iter() {
            let term_is_true = try_str!(
              eval.eval(& term),
              "[Step::k_split] could not evaluate term {:?} in current model", term
            ) ;
            if ! term_is_true {
              // Falsified, remove from `map` and put in `rest`.
              match map.remove(& term) {
                Some( (info, _) ) => {
                  let pre = rest.insert(term, info) ;
                  debug_assert!( pre.is_none() )
                },
                None => return Err(
                  format!(
                    "[Step::k_split] unknown term {:?} in `to_check`", term
                  )
                ),
              }
            }
          }
        }

        try_str!(
          self.unroller.deactivate(actlit),
          "[Step::k_split] could not deactivate negative actlit"
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
      let k = self.unroll_len() ;
      match Step::<Val, Solver>::setup(& mut self.unroller, k) {
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
      self.k.curr().to_usize()
    }
    fn unroll(& mut self) -> Res<usize> {
      self.k = self.k.nxt() ;
      try_str!(
        self.unroller.unroll(& self.k),
        "while unrolling system at {}", self.k.next()
      ) ;
      Ok( self.unroll_len() )
    }
    fn add_invs(& mut self, invs: STermSet) -> Res<()> {
      self.unroller.add_invs(invs, & self.check, & self.k)
    }
  }
}