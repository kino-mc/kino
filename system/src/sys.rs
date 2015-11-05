// Copyright 2015 Adrien Champion. See the COPYRIGHT file at the top-level
// directory of this distribution.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use std::collections::HashMap ;

use term::{ Factory, Sym, Term, Type } ;

use super::{ State, Pred } ;

pub struct Uf {
  sig: Vec<Type>,
  typ: Type,
}
impl Uf {
  pub fn mk(sig: Vec<Type>, typ: Type) -> Self {
    Uf { sig: sig, typ: typ }
  }
  pub fn sig(& self) -> & [ Type ] { & self.sig }
  pub fn typ(& self) -> & Type { & self.typ }
}

pub struct Fun {
  args: Vec<(Sym, Type)>,
  typ: Type,
}
impl Fun {
  pub fn mk(args: Vec<(Sym, Type)>, typ: Type) -> Self {
    Fun { args: args, typ: typ }
  }
  pub fn args(& self) -> & [ (Sym, Type) ] { & self.args }
  pub fn typ(& self) -> & Type { & self.typ }
}

pub struct SubSys {
  sym: Sym,
  state: State,
  sub_sys: HashMap<Sym, SubSys>,
  preds: Vec<Pred>,
  init: Term,
  trans: Term,
}
impl SubSys {
  pub fn mk(
    sym: Sym, state: State,
    sub_sys: HashMap<Sym, SubSys>,
    preds: Vec<Pred>, init: Term, trans: Term
  ) -> Self {
    SubSys {
      sym: sym, state: state, sub_sys: sub_sys,
      preds: preds, init: init, trans: trans
    }
  }
  pub fn sym(& self) -> & Sym {
    & self.sym
  }
  pub fn state(& self) -> & State {
    & self.state
  }
  pub fn sub_sys(& self) -> & HashMap<Sym, SubSys> {
    & self.sub_sys
  }
  pub fn preds(& self) -> & [ Pred ] {
    & self.preds
  }
  pub fn init(& self) -> & Term {
    & self.init
  }
  pub fn trans(& self) -> & Term {
    & self.trans
  }
}

pub struct Sys {
  factory: Factory,
  sym: Sym,
  state: State,
  ufs: Vec<Uf>,
  funs: Vec<Fun>,
  sub_sys: HashMap<Sym, SubSys>,
  preds: Vec<Pred>,
  init: Term,
  trans: Term,
}
impl Sys {
  pub fn mk(
    factory: Factory, sym: Sym, state: State,
    ufs: Vec<Uf>, funs: Vec<Fun>,
    sub_sys: HashMap<Sym, SubSys>,
    preds: Vec<Pred>,
    init: Term,
    trans: Term,
  ) -> Self {
    Sys {
      factory: factory,
      sym: sym,
      state: state,
      ufs: ufs,
      funs: funs,
      sub_sys: sub_sys,
      preds: preds,
      init: init,
      trans: trans,
    }
  }
  pub fn sym(& self) -> & Sym {
    & self.sym
  }
  pub fn state(& self) -> & State {
    & self.state
  }
  pub fn ufs(& self) -> & [ Uf ] {
    & self.ufs
  }
  pub fn funs(& self) -> & [ Fun ] {
    & self.funs
  }
  pub fn sub_sys(& self) -> & HashMap<Sym, SubSys> {
    & self.sub_sys
  }
  pub fn preds(& self) -> & [ Pred ] {
    & self.preds
  }
  pub fn init(& self) -> & Term {
    & self.init
  }
  pub fn trans(& self) -> & Term {
    & self.trans
  }
}