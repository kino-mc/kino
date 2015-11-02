// Copyright 2015 Adrien Champion. See the COPYRIGHT file at the top-level
// directory of this distribution.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use std::io ;
use std::thread::sleep_ms ;
use std::collections::{ HashSet, HashMap } ;

use term::{ Sym, Type, Term, Factory } ;

#[derive(Clone)]
pub struct Sig {
  types: Vec<Type>,
}
impl Sig {
  #[inline(always)]
  pub fn mk(types: Vec<Type>) -> Self {
    Sig { types: types }
  }
  #[inline(always)]
  pub fn types(& self) -> & [Type] { & self.types }
}

#[derive(Clone)]
pub struct Args {
  args: Vec<(Sym, Type)>,
}
impl Args {
  #[inline(always)]
  pub fn mk(args: Vec<(Sym, Type)>) -> Self {
    Args { args: args }
  }
  #[inline(always)]
  pub fn args(& self) -> & [(Sym, Type)] { & self.args }
}

#[derive(Clone)]
pub struct State {
  sym: Sym,
  args: Args,
}
impl State {
  #[inline(always)]
  pub fn mk(sym: Sym, args: Args) -> Self {
    State { sym: sym, args: args }
  }
  #[inline(always)]
  pub fn sym(& self) -> & Sym { & self.sym }
  #[inline(always)]
  pub fn args(& self) -> & [(Sym, Type)] { self.args.args() }
}

#[derive(Clone)]
pub struct FunDec {
  sym: Sym,
  sig: Sig,
  typ: Type,
}
impl FunDec {
  #[inline(always)]
  pub fn mk(sym: Sym, sig: Sig, typ: Type) -> Self {
    FunDec { sym: sym, sig: sig, typ: typ }
  }
  #[inline(always)]
  pub fn sym(& self) -> & Sym { & self.sym }
  #[inline(always)]
  pub fn sig(& self) -> & [Type] { & self.sig.types() }
  #[inline(always)]
  pub fn typ(& self) -> & Type { & self.typ }
}

#[derive(Clone)]
pub struct Body {
  body: Term,
  calls: Vec<Sym>,
}
impl Body {
  /** Add calls in constructor late. */
  #[inline(always)]
  pub fn mk(body: Term) -> Self {
    Body { body: body, calls: vec![] }
  }
  #[inline(always)]
  pub fn body(& self) -> & Term { & self.body }
  #[inline(always)]
  pub fn calls(& self) -> & [Sym] { & self.calls }
}

#[derive(Clone)]
pub struct FunDef {
  sym: Sym,
  args: Args,
  typ: Type,
  body: Body,
}
impl FunDef {
  #[inline(always)]
  pub fn mk(sym: Sym, args: Args, typ: Type, body: Body) -> Self {
    FunDef { sym: sym, args: args, typ: typ, body: body }
  }
  #[inline(always)]
  pub fn sym(& self) -> & Sym { & self.sym }
  #[inline(always)]
  pub fn args(& self) -> & [(Sym, Type)] { & self.args.args() }
  #[inline(always)]
  pub fn typ(& self) -> & Type { & self.typ }
  #[inline(always)]
  pub fn body(& self) -> & Body { & self.body }
}

#[derive(Clone)]
pub struct Pred {
  sym: Sym,
  state: Sym,
  body: Body,
}
impl Pred {
  #[inline(always)]
  pub fn mk(sym: Sym, state: Sym, body: Body) -> Self {
    Pred { sym: sym, state: state, body: body }
  }
  #[inline(always)]
  pub fn sym(& self) -> & Sym { & self.sym }
  #[inline(always)]
  pub fn state(& self) -> & Sym { & self.state }
  #[inline(always)]
  pub fn body(& self) -> & Body { & self.body }
}

#[derive(Clone)]
pub struct Init {
  sym: Sym,
  state: Sym,
  body: Body,
}
impl Init {
  #[inline(always)]
  pub fn mk(sym: Sym, state: Sym, body: Body) -> Self {
    Init { sym: sym, state: state, body: body }
  }
  #[inline(always)]
  pub fn sym(& self) -> & Sym { & self.sym }
  #[inline(always)]
  pub fn state(& self) -> & Sym { & self.state }
  #[inline(always)]
  pub fn body(& self) -> & Body { & self.body }
}

#[derive(Clone)]
pub struct Trans {
  sym: Sym,
  state: Sym,
  body: Body,
}
impl Trans {
  #[inline(always)]
  pub fn mk(sym: Sym, state: Sym, body: Body) -> Self {
    Trans { sym: sym, state: state, body: body }
  }
  #[inline(always)]
  pub fn sym(& self) -> & Sym { & self.sym }
  #[inline(always)]
  pub fn state(& self) -> & Sym { & self.state }
  #[inline(always)]
  pub fn body(& self) -> & Body { & self.body }
}

#[derive(Clone)]
pub struct Sys {
  sym: Sym,
  state: Sym,
  init: Sym,
  trans: Sym,
}
impl Sys {
  #[inline(always)]
  pub fn mk(sym: Sym, state: Sym, init: Sym, trans: Sym) -> Self {
    Sys { sym: sym, state: state, init: init, trans: trans }
  }
  #[inline(always)]
  pub fn sym(& self) -> & Sym { & self.sym }
  #[inline(always)]
  pub fn state(& self) -> & Sym { & self.state }
  #[inline(always)]
  pub fn init(& self) -> & Sym { & self.init }
  #[inline(always)]
  pub fn trans(& self) -> & Sym { & self.trans }
}

pub enum Item {
  St(State),
  FDc(FunDec),
  FDf(FunDef),
  P(Pred),
  I(Init),
  T(Trans),
  S(Sys),
}
impl Item {
  pub fn sym(& self) -> & Sym {
    use base::Item::* ;
    match * self {
      St(ref bla) => bla.sym(),
      FDc(ref bla) => bla.sym(),
      FDf(ref bla) => bla.sym(),
      P(ref bla) => bla.sym(),
      I(ref bla) => bla.sym(),
      T(ref bla) => bla.sym(),
      S(ref bla) => bla.sym(),
    }
  }
}

pub enum Callable {
  Dec(FunDec),
  Def(FunDef),
}

pub struct Context {
  buffer: Vec<u8>,
  factory: Factory,
  all: HashSet<Sym>,
  states: HashMap<Sym, State>,
  callables: HashMap<Sym, Callable>,
  preds: HashMap<Sym, Pred>,
  inits: HashMap<Sym, Init>,
  transs: HashMap<Sym, Trans>,
  syss: HashMap<Sym, Sys>,
}
impl Context {
  pub fn mk(factory: Factory, buffer: usize) -> Self {
    Context {
      buffer: Vec::with_capacity(buffer),
      factory: factory,
      all: HashSet::new(),
      states: HashMap::new(),
      callables: HashMap::new(),
      preds: HashMap::new(),
      inits: HashMap::new(),
      transs: HashMap::new(),
      syss: HashMap::new(),
    }
  }

  // pub fn read(
  //   & mut self, reader: & mut io::Read
  // ) -> io::Result< Option<(Sym, Vec<Sym>, Vec<Sym>)> > {
  //   use nom::IResult::* ;
  //   loop {
  //     match reader.read(& mut buffer) {
  //       Ok(0) => sleep_ms(100u32),
  //       Ok(n) => match item_parser(& self.buffer, self.factory) {
  //         Done(chars, item) => self.add
  //       },
  //       Err(e) => return Err(e),
  //     }
  //   }
  // }

  fn check(& self, sym: & Sym) -> Result<(),Item> {
    use self::Item::* ;
    use self::Callable::* ;
    if self.all.contains(sym) {
      match self.states.get(sym) {
        None => (),
        Some(ref state) => return Err( St((* state).clone()) ),
      } ;
      match self.callables.get(sym) {
        None => (),
        Some(& Dec(ref f)) => return Err( FDc(f.clone()) ),
        Some(& Def(ref f)) => return Err( FDf(f.clone()) ),
      } ;
      match self.preds.get(sym) {
        None => (),
        Some(pred) => return Err( P(pred.clone()) ),
      } ;
      match self.inits.get(sym) {
        None => (),
        Some(init) => return Err( I(init.clone()) ),
      } ;
      match self.transs.get(sym) {
        None => (),
        Some(trans) => return Err( T(trans.clone()) ),
      } ;
      match self.syss.get(sym) {
        None => (),
        Some(sys) => return Err( S(sys.clone()) ),
      } ;
      panic!("symbol {:?} is in all but nowhere else", sym)
    } else {
      Ok(())
    }
  }
}

pub trait CanAdd<T> {
  fn add(& mut self, T) -> Result<(),(Item,Item)> ;
}

impl CanAdd<Item> for Context {
  fn add(& mut self, i: Item) -> Result<(),(Item,Item)> {
    use base::Item::* ;
    match i {
      St(bla) => self.add(bla),
      FDc(bla) => self.add(bla),
      FDf(bla) => self.add(bla),
      P(bla) => self.add(bla),
      I(bla) => self.add(bla),
      T(bla) => self.add(bla),
      S(bla) => self.add(bla),
    }
  }
}

macro_rules! impl_add {
  ($input:ident, ($slf:ident, $i:ident) -> $b:block, $err:ident) => (
    impl CanAdd<$input> for Context {
      fn add(& mut $slf, $i: $input) -> Result<(),(Item,Item)> {
        match $slf.check($i.sym()) {
          Ok(()) => {
            $slf.all.insert($i.sym().clone()) ;
            $b ;
            Ok(())
          },
          Err(e) => Err( (Item::$err($i), e) ),
        }
      }
    }
  ) ;
  ($input:ident, $map:ident, $err:ident) => (
    impl_add!{
      $input, (self, i) -> { self.$map.insert(i.sym().clone(), i) }, $err
    }
  )
}

impl_add!{ State, states, St }
impl_add!{
  FunDef,
  (self, i) -> {
    self.callables.insert( i.sym().clone(), Callable::Def(i) )
  },
  FDf
}
impl_add!{
  FunDec,
  (self, i) -> {
    self.callables.insert( i.sym().clone(), Callable::Dec(i) )
  },
  FDc
}
impl_add!{ Pred, preds, P }
impl_add!{ Init, inits, I }
impl_add!{ Trans, transs, T }
impl_add!{ Sys, syss, S }
