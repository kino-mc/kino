// Copyright 2015 Adrien Champion. See the COPYRIGHT file at the top-level
// directory of this distribution.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! Candidate term mining functions.

use std::collections::{ HashMap, HashSet } ;

use term::{
  Factory, Term, STerm, TermSet, STermSet, Type, Sym, Cst
} ;

use system::Sys ;

use common::errors::* ;

/// A set of symbols.
pub type SymSet = HashSet<Sym> ;
/// A set of constants.
pub type CstSet = HashSet<Cst> ;
/// A map from types to something.
pub type TypMap<T> = HashMap<Type, T> ;

/// Mining information for a type.
pub struct Info {
  /// State variables.
  vars: SymSet,
  /// Constants.
  csts: CstSet,
  /// Terms.
  trms: STermSet,
}
impl Info {
  /// Creates a empty info with some capacity.
  #[inline]
  pub fn empty(capa: usize) -> Self {
    Info {
      vars: SymSet::with_capacity(capa),
      csts: CstSet::with_capacity(capa),
      trms: STermSet::with_capacity(capa),
    }
  }
  /// Shrinks the sets to their current size.
  #[inline]
  pub fn shrink(& mut self) {
    self.vars.shrink_to_fit() ;
    self.csts.shrink_to_fit() ;
    self.trms.shrink_to_fit()
  }
  /// Adds a variable.
  #[inline]
  pub fn add_svar(& mut self, svar: & Sym) {
    self.vars.insert( svar.clone() ) ;
    ()
  }
  /// Adds a constant.
  #[inline]
  pub fn add_cst(& mut self, cst: Cst) {
    self.csts.insert( cst.clone() ) ;
    ()
  }
  /// Adds a term.
  #[inline]
  pub fn add_term(& mut self, term: STerm) {
    self.trms.insert( term ) ;
    ()
  }

  /// State variables.
  #[inline]
  pub fn svars(& self) -> & SymSet {
    & self.vars
  }
  /// Constants.
  #[inline]
  pub fn csts(& self) -> & CstSet {
    & self.csts
  }
  /// Terms.
  #[inline]
  pub fn trms(& self) -> & STermSet {
    & self.trms
  }
}

/// Information returned by mining.
pub struct Miner {
  /// System the mining's for.
  sys: Sys,
  /// Term factory.
  fac: Factory,
  /// Boolean info.
  boo: Info,
  /// Int info.
  int: Info,
  /// Rat info.
  rat: Info,
}
impl Miner {
  /// Creates a miner from a system.
  #[inline]
  pub fn mk(sys: & Sys, factory: & Factory, all_out: bool) -> Self {
    use term::{
      VarMaker, CstMaker, Int, Rat, Zero, One, UnTermOps, State, STerm
    } ;
    let mut boo = Info::empty(17) ;
    let mut int = Info::empty(17) ;
    let mut rat = Info::empty(17) ;

    // Splitting state variables of the system.
    for & (ref sym, ref typ) in sys.state().args().iter() {
      use term::Type::* ;
      match * typ.get() {
        Bool => {
          boo.add_svar(sym) ;
          let svar_term: Term = factory.svar(sym.get().clone(), State::Curr) ;
          let svar = STerm::One(
            svar_term.clone(), factory.bump(& svar_term).unwrap()
          ) ;
          boo.add_term( svar ) ;
          let svar_term: Term = factory.not(svar_term) ;
          let svar = STerm::One(
            svar_term.clone(), factory.bump(svar_term).unwrap()
          ) ;
          boo.add_term( svar )
        },
        Int  => {
          int.add_svar(sym) ;
          let svar_term: Term = factory.svar(sym.get().clone(), State::Curr) ;
          let svar = STerm::One(
            svar_term.clone(), factory.bump(& svar_term).unwrap()
          ) ;
          int.add_term( svar ) ;
          let svar_term: Term = factory.neg(svar_term) ;
          let svar = STerm::One(
            svar_term.clone(), factory.bump(svar_term).unwrap()
          ) ;
          int.add_term( svar )
        },
        Rat  => {
          rat.add_svar(sym) ;
          let svar_term: Term = factory.svar(sym.get().clone(), State::Curr) ;
          let svar = STerm::One(
            svar_term.clone(), factory.bump(& svar_term).unwrap()
          ) ;
          rat.add_term( svar ) ;
          let svar_term: Term = factory.neg(svar_term) ;
          let svar = STerm::One(
            svar_term.clone(), factory.bump(svar_term).unwrap()
          ) ;
          rat.add_term( svar )
        },
      }
    }

    boo.add_cst( factory.cst(true) ) ;
    boo.add_cst( factory.cst(false) ) ;

    let (zero, one) = ( Int::zero(), Int::one() ) ;

    int.add_cst( factory.cst(zero.clone()) ) ;
    int.add_cst( factory.cst(one.clone()) ) ;
    int.add_cst( factory.cst(one.clone() + one.clone()) ) ;

    let (zero, one) = (
      Rat::new(zero, one.clone()), Rat::new(one.clone(), one)
    ) ;

    rat.add_cst( factory.cst(zero) ) ;
    rat.add_cst( factory.cst(one.clone()) ) ;
    rat.add_cst( factory.cst(one.clone() + one) ) ;

    // Extracting constants.
    let mut miner = factory.cst_fold(
      Miner {
        sys: sys.clone(),
        fac: factory.clone(),
        boo: boo,
        int: int,
        rat: rat,
      }, | mut miner, cst | {
        use term::Type::* ;
        match cst.typ() {
          Bool => (),
          Int  => miner.int.add_cst( cst.clone() ),
          Rat  => miner.rat.add_cst( cst.clone() ),
        }
        miner
      }
    ) ;

    if all_out {

      // Add svar le/lt/ge/gt cst for int and rat to boo.
      for svar in miner.int.vars.iter() {
        for cst in miner.int.csts.iter() {
          let svar_term: Term = factory.svar(svar.clone(), State::Curr) ;
          let cst = factory.cst(cst.clone()) ;
          let term = factory.le(svar_term.clone(), cst.clone()) ;
          let term = STerm::One(
            term.clone(), factory.bump(& term).unwrap()
          ) ;
          miner.boo.add_term( term ) ;
          let term = factory.lt(svar_term.clone(), cst.clone()) ;
          let term = STerm::One(
            term.clone(), factory.bump(& term).unwrap()
          ) ;
          miner.boo.add_term( term ) ;
          let term = factory.gt(svar_term.clone(), cst.clone()) ;
          let term = STerm::One(
            term.clone(), factory.bump(& term).unwrap()
          ) ;
          miner.boo.add_term( term ) ;
          let term = factory.ge(svar_term, cst) ;
          let term = STerm::One(
            term.clone(), factory.bump(& term).unwrap()
          ) ;
          miner.boo.add_term( term ) ;
        }
      }
      for svar in miner.rat.vars.iter() {
        for cst in miner.rat.csts.iter() {
          let svar_term: Term = factory.svar(svar.clone(), State::Curr) ;
          let cst = factory.cst(cst.clone()) ;
          let term = factory.le(svar_term.clone(), cst.clone()) ;
          let term = STerm::One(
            term.clone(), factory.bump(& term).unwrap()
          ) ;
          miner.boo.add_term( term ) ;
          let term = factory.lt(svar_term.clone(), cst.clone()) ;
          let term = STerm::One(
            term.clone(), factory.bump(& term).unwrap()
          ) ;
          miner.boo.add_term( term ) ;
          let term = factory.gt(svar_term.clone(), cst.clone()) ;
          let term = STerm::One(
            term.clone(), factory.bump(& term).unwrap()
          ) ;
          miner.boo.add_term( term ) ;
          let term = factory.ge(svar_term, cst) ;
          let term = STerm::One(
            term.clone(), factory.bump(& term).unwrap()
          ) ;
          miner.boo.add_term( term ) ;
        }
      }

    }

    miner
  }
  /// Shrinks the sets to the current size.
  #[inline]
  pub fn shrink(& mut self) {
    self.boo.shrink() ;
    self.int.shrink() ;
    self.rat.shrink()
  }

  /// Extracts the set of candidates terms from a miner.
  ///
  /// First is bool, then int, and finally rat.
  #[inline]
  pub fn to_sets(self) -> (STermSet, STermSet, STermSet) {
    (self.boo.trms, self.int.trms, self.rat.trms)
  }

  /// The system this info's for.
  #[inline]
  pub fn sys(& self) -> & Sys { & self.sys }

  /// Bool info.
  #[inline]
  pub fn bool_info(& self) -> & Info {
    & self.boo
  }
  /// Int info.
  #[inline]
  pub fn int_info(& self) -> & Info {
    & self.int
  }
  /// Rat info.
  #[inline]
  pub fn rat_info(& self) -> & Info {
    & self.rat
  }

  /// Adds candidate terms of the form `<var> +- <var'>`, `<var> +- <cst>`,
  /// and `<cst> - <var>`.
  /// (One-state.)
  fn arith_synth_os_oct2<
    F: Fn(& Cst) -> bool
  >(
    factory: & Factory, info: & mut Info, cst_ignore: F
  ) -> Res<()> {
    // Allocating more space based on a rough estimate.
    let guesstimate = info.vars.len() * info.csts.len() ;
    let free = info.trms.capacity() - info.trms.len() ;
    if free < guesstimate {
      info.trms.reserve(guesstimate - free)
    }

    let mut svar_iter = info.vars.iter() ;

    while let Some(var) = svar_iter.next() {
      use term::{ VarMaker, UnTermOps } ;
      use term::State ;
      let var: Term = factory.svar( var.clone(), State::Curr ) ;

      // `<var> +- <var'>`
      for var_p in svar_iter.clone() {
        let var_p: Term = factory.svar( var_p.clone(), State::Curr ) ;
        let add = factory.add(
          vec![ var.clone(), var_p.clone() ]
        ) ;
        let sub = factory.sub(
          vec![ var.clone(), var_p.clone() ]
        ) ;
        info.trms.insert(
          STerm::One(
            add.clone(), try!( factory.bump(add) )
          )
        ) ;
        info.trms.insert(
          STerm::One(
            sub.clone(), try!( factory.bump(sub) )
          )
        ) ;
        ()
      }

      // `<var> +- <cst>`
      for cst in info.csts.iter() {
        if cst_ignore( cst ) {
          let cst = factory.mk_cst( cst.clone() ) ;
          let add = factory.add(
            vec![ var.clone(), cst.clone() ]
          ) ;
          let sub = factory.sub(
            vec![ var.clone(), cst.clone() ]
          ) ;
          info.trms.insert(
            STerm::One(
              add.clone(), try!( factory.bump(add) )
            )
          ) ;
          info.trms.insert(
            STerm::One(
              sub.clone(), try!( factory.bump(sub) )
            )
          ) ;
          ()
        }
      }
    }

    Ok(())
  }

  /// Adds int candidate terms of the form `<var> +- <var'>`, `<var> +- <cst>`,
  /// and `<cst> - <var>`.
  /// (One-state.)
  fn int_synth_os_oct2(& mut self) -> Res<()> {
    use term::{ Int, Zero } ;
    use term::real_term::Cst as RCst ;
    let zero = RCst::Int( Int::zero() ) ;

    Self::arith_synth_os_oct2(
      & self.fac, & mut self.int, |cst| * cst.get() != zero
    )
  }

  /// Adds rat candidate terms of the form `<var> +- <var'>`, `<var> +- <cst>`,
  /// and `<cst> - <var>`.
  /// (One-state.)
  fn rat_synth_os_oct2(& mut self) -> Res<()> {
    use term::{ Rat, Zero } ;
    use term::real_term::Cst as RCst ;
    let zero = RCst::Rat( Rat::zero() ) ;

    Self::arith_synth_os_oct2(
      & self.fac, & mut self.rat, |cst| * cst.get() != zero
    )
  }

  /// Generates bool candidate terms of the form `<int> >/>=/</<= 0` where
  /// `<int>` is an int candidate term.
  fn bool_synth_of_int(& mut self) {
    use term::{ OpMaker, CstMaker, Int, Zero } ;
    use term::Operator::{ Lt, Le, Ge, Gt } ;
    let factory = self.fac.clone() ;
    let zero: Term = factory.cst( Int::zero() ) ;

    let synth = | term: & Term, op | factory.op(
      op, vec![ term.clone(), zero.clone() ]
    ) ;

    for int in self.int.trms.iter() {
      match * int {
        STerm::One(ref curr, ref next) => {
          self.boo.trms.insert(
            STerm::One( synth(curr, Lt), synth(next, Lt) )
          ) ;
          self.boo.trms.insert(
            STerm::One( synth(curr, Le), synth(next, Lt) )
          ) ;
          self.boo.trms.insert(
            STerm::One( synth(curr, Ge), synth(next, Lt) )
          ) ;
          self.boo.trms.insert(
            STerm::One( synth(curr, Gt), synth(next, Lt) )
          ) ;
          ()
        },
        STerm::Two(ref next) => {
          self.boo.trms.insert(
            STerm::Two( synth(next, Lt) )
          ) ;
          self.boo.trms.insert(
            STerm::Two( synth(next, Lt) )
          ) ;
          self.boo.trms.insert(
            STerm::Two( synth(next, Lt) )
          ) ;
          self.boo.trms.insert(
            STerm::Two( synth(next, Lt) )
          ) ;
          ()
        },
      }
    }
  }
}

/// Mines a system for boolean candidate terms.
pub fn bool(factory: & Factory, sys: & Sys, all_out: bool) -> (Term, TermSet) {
  use term::CstMaker ;
  let mut miner = Miner::mk(sys, factory, all_out) ;
  if all_out {
    match miner.int_synth_os_oct2() {
      Ok(()) => (),
      Err(e) => panic!(
        "[mine::bool] in call to `Miner::int_synth_os_oct2`: {}", e
      )
    } ;
    match miner.rat_synth_os_oct2() {
      Ok(()) => (),
      Err(e) => panic!(
        "[mine::bool] in call to `Miner::rat_synth_os_oct2`: {}", e
      )
    }
  }
  miner.bool_synth_of_int() ;
  let (set, _, _) = miner.to_sets() ;

  let mut set: TermSet = set.into_iter().filter_map(
    |sterm| match sterm {
      STerm::One(_, nxt) => Some(nxt),
      STerm::Two(_) => None,
    }
  ).collect() ;

  let rep = factory.cst(false) ;
  set.remove(& rep) ;
  set.insert( factory.cst(true) ) ;
  (rep, set)
}