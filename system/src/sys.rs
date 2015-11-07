// Copyright 2015 Adrien Champion. See the COPYRIGHT file at the top-level
// directory of this distribution.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use std::collections::HashMap ;
use std::sync::{ Arc, RwLock } ;

use term::{ Factory, Sym, Term, Type } ;

use base::{ Prop, Callable, Args } ;
use base::Sys as System ;

// pub struct Uf {
//   sig: Vec<Type>,
//   typ: Type,
// }
// impl Uf {
//   pub fn mk(sig: Vec<Type>, typ: Type) -> Self {
//     Uf { sig: sig, typ: typ }
//   }
//   pub fn sig(& self) -> & [ Type ] { & self.sig }
//   pub fn typ(& self) -> & Type { & self.typ }
// }

// pub struct Fun {
//   args: Vec<(Sym, Type)>,
//   typ: Type,
// }
// impl Fun {
//   pub fn mk(args: Vec<(Sym, Type)>, typ: Type) -> Self {
//     Fun { args: args, typ: typ }
//   }
//   pub fn args(& self) -> & [ (Sym, Type) ] { & self.args }
//   pub fn typ(& self) -> & Type { & self.typ }
// }

// pub struct SubSys {
//   sym: Sym,
//   state: State,
//   sub_sys: HashMap<Sym, SubSys>,
//   preds: Vec<Pred>,
//   init: Term,
//   trans: Term,
// }
// impl SubSys {
//   pub fn mk(
//     sym: Sym, state: State,
//     sub_sys: HashMap<Sym, SubSys>,
//     preds: Vec<Pred>, init: Term, trans: Term
//   ) -> Self {
//     SubSys {
//       sym: sym, state: state, sub_sys: sub_sys,
//       preds: preds, init: init, trans: trans
//     }
//   }
//   pub fn sym(& self) -> & Sym {
//     & self.sym
//   }
//   pub fn state(& self) -> & State {
//     & self.state
//   }
//   pub fn sub_sys(& self) -> & HashMap<Sym, SubSys> {
//     & self.sub_sys
//   }
//   pub fn preds(& self) -> & [ Pred ] {
//     & self.preds
//   }
//   pub fn init(& self) -> & Term {
//     & self.init
//   }
//   pub fn trans(& self) -> & Term {
//     & self.trans
//   }
// }

pub type SafeSys = RwLock<Arc<System>> ;

pub struct Sys {
  factory: Factory,
  sys: SafeSys,
  init: Term,
  trans: Term,
}
// pub trait SysMaker {
//   fn mk(Factory, SafeSys) -> Self ;
// }

impl Sys {
  #[inline(always)]
  pub fn mk(factory: Factory, sys: Arc<System>) -> Self {
    use term::State ;
    use term::VarMaker ;
    use term::AppMaker ;
    use std::iter::Extend ;
    // Constructing init and trans applications.
    let (init, trans) = {
      let sym = sys.sym() ;
      let args = sys.state() ;
      let mut params_init = Vec::with_capacity(args.len()) ;
      let mut params_trans = Vec::with_capacity(args.len() * 2) ;
      let mut params_trans_next = Vec::with_capacity(args.len()) ;
      for & (ref sym, _) in args.args().iter() {
        let var_0 = factory.svar(sym.clone(), State::Curr) ;
        let var_1 = factory.svar(sym.clone(), State::Next) ;
        params_init.push(var_0.clone()) ;
        params_trans.push(var_0) ;
        params_trans_next.push(var_1) ;
      } ;
      params_trans.extend(params_trans_next) ;
      (
        factory.app(sym.clone(), params_init),
        factory.app(sym.clone(), params_trans)
      )
    } ;
    Sys {
      factory: factory, sys: RwLock::new(sys), init: init, trans: trans
    }
  }
  #[inline(always)]
  pub fn sym<T, F: Fn(& Sym) -> T>(& self, f: F) -> T {
    f( self.sys.read().unwrap().sym() )
  }
  #[inline(always)]
  pub fn state<T, F: Fn(& Args) -> T>(& self, f: F) -> T {
    f( self.sys.read().unwrap().state() )
  }

  pub fn init(& self) -> & Term { & self.init }
  pub fn trans(& self) -> & Term { & self.trans }
  // #[inline(always)]
  // pub fn calls(& self) -> & [ Uf ] {
  //   & self.ufs.read().unwrap().
  // }
  // pub fn sub_sys(& self) -> & HashMap<Sym, SubSys> {
  //   & self.sub_sys
  // }
  // pub fn preds(& self) -> & [ Prop ] {
  //   & self.preds
  // }
  // pub fn init(& self) -> & Term {
  //   & self.init
  // }
  // pub fn trans(& self) -> & Term {
  //   & self.trans
  // }
}