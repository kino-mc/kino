// Copyright 2015 Adrien Champion. See the COPYRIGHT file at the top-level
// directory of this distribution.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use std::fmt ;

use term::{ Sym, Type, StsResult } ;


#[derive(Debug,Clone)]
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
impl fmt::Display for Sig {
  fn fmt(& self, fmt: & mut fmt::Formatter) -> fmt::Result {
    try!( write!(fmt, "(") ) ;
    let mut iter = self.types.iter() ;
    if let Some(ref t) = iter.next() {
      try!( write!(fmt, "{}", t) ) ;
      for t in iter {
        try!( write!(fmt, " {}", t) )
      }
    } ;
    write!(fmt, ")")
  }
}

#[derive(Debug,Clone)]
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
impl fmt::Display for Args {
  fn fmt(& self, fmt: & mut fmt::Formatter) -> fmt::Result {
    try!( write!(fmt, "(") ) ;
    let mut iter = self.args.iter() ;
    if let Some( & (ref s, ref t) ) = iter.next() {
      try!( write!(fmt, "({} {})", s, t) ) ;
      for & ( ref s, ref t) in iter {
        try!( write!(fmt, " ({} {})", s, t) )
      }
    } ;
    write!(fmt, ")")
  }
}

#[derive(Debug,Clone)]
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
impl fmt::Display for State {
  fn fmt(& self, fmt: & mut fmt::Formatter) -> fmt::Result {
    write!(fmt, "{}: {}", self.sym, self.args)
  }
}

#[derive(Debug,Clone)]
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
impl fmt::Display for FunDec {
  fn fmt(& self, fmt: & mut fmt::Formatter) -> fmt::Result {
    write!(fmt, "{}{} -> {}", self.sym, self.sig, self.typ)
  }
}

#[derive(Debug,Clone)]
pub struct Body {
  body: StsResult,
  calls: Vec<Sym>,
}
impl Body {
  /** Add calls in constructor late. */
  #[inline(always)]
  pub fn mk(body: StsResult) -> Self {
    Body { body: body, calls: vec![] }
  }
  #[inline(always)]
  pub fn body(& self) -> & StsResult { & self.body }
  #[inline(always)]
  pub fn calls(& self) -> & [Sym] { & self.calls }
}
impl fmt::Display for Body {
  fn fmt(& self, fmt: & mut fmt::Formatter) -> fmt::Result {
    write!(fmt, "{}", self.body)
  }
}

#[derive(Debug,Clone)]
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
impl fmt::Display for FunDef {
  fn fmt(& self, fmt: & mut fmt::Formatter) -> fmt::Result {
    write!(
      fmt, "{}{} -> {} {{ {} }}", self.sym, self.args, self.typ, self.body
    )
  }
}

#[derive(Debug,Clone)]
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
impl fmt::Display for Pred {
  fn fmt(& self, fmt: & mut fmt::Formatter) -> fmt::Result {
    write!(
      fmt, "{}({}) {{ {} }}", self.sym, self.state, self.body
    )
  }
}

#[derive(Debug,Clone)]
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
impl fmt::Display for Init {
  fn fmt(& self, fmt: & mut fmt::Formatter) -> fmt::Result {
    write!(
      fmt, "{}({}) {{ {} }}", self.sym, self.state, self.body
    )
  }
}

#[derive(Debug,Clone)]
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
impl fmt::Display for Trans {
  fn fmt(& self, fmt: & mut fmt::Formatter) -> fmt::Result {
    write!(
      fmt, "{}({}) {{ {} }}", self.sym, self.state, self.body
    )
  }
}

#[derive(Debug,Clone)]
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
impl fmt::Display for Sys {
  fn fmt(& self, fmt: & mut fmt::Formatter) -> fmt::Result {
    write!(
      fmt, "{}({}) {{ {} -> {} }}",
      self.sym, self.state, self.init, self.trans
    )
  }
}

#[derive(Debug,Clone)]
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
  pub fn desc(& self) -> & 'static str {
    use base::Item::* ;
    match * self {
      St(_) => "state definition",
      FDc(_) => "function declaration",
      FDf(_) => "function definition",
      P(_) => "predicate definition",
      I(_) => "init definition",
      T(_) => "trans definition",
      S(_) => "system definition",
    }
  }
  pub fn state(& self) -> Option<& Sym> {
    use base::Item::* ;
    match * self {
      P(ref e) => Some( e.state() ),
      I(ref e) => Some( e.state() ),
      T(ref e) => Some( e.state() ),
      S(ref e) => Some( e.state() ),
      _ => None,
    }
  }
}

pub enum Callable {
  Dec(FunDec),
  Def(FunDef),
}
impl Callable {
  pub fn sym(& self) -> & Sym {
    match * self {
      Callable::Def(ref f) => f.sym(),
      Callable::Dec(ref f) => f.sym(),
    }
  }
}
impl fmt::Display for Callable {
  fn fmt(& self, fmt: & mut fmt::Formatter) -> fmt::Result {
    match * self {
      Callable::Dec(ref f) => write!(fmt, "declaration : {}", f),
      Callable::Def(ref f) => write!(fmt, "definition  : {}", f),
    }
  }
}