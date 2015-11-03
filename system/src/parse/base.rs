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

/** A signature: a list of types. Used in `FunDec`. */
#[derive(Debug,Clone)]
pub struct Sig {
  /** Types of the signature. */
  types: Vec<Type>,
}
impl Sig {
  /** Creates a new signature. */
  #[inline(always)]
  pub fn mk(types: Vec<Type>) -> Self {
    Sig { types: types }
  }
  /** The types of the anonymous signature. */
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

/** A list of arguments. */
#[derive(Debug,Clone)]
pub struct Args {
  /** The symbol/type pair list. */
  args: Vec<(Sym, Type)>,
}
impl Args {
  /** Creates a new argument list. */
  #[inline(always)]
  pub fn mk(args: Vec<(Sym, Type)>) -> Self {
    Args { args: args }
  }
  /** The symbol/type pair list. */
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

/** A state. */
#[derive(Debug,Clone)]
pub struct State {
  /** Identifier of the state. */
  sym: Sym,
  /** Signature of the state. */
  args: Args,
}
impl State {
  /** Creates a new state. */
  #[inline(always)]
  pub fn mk(sym: Sym, args: Args) -> Self {
    State { sym: sym, args: args }
  }
  /** Identifier of the state. */
  #[inline(always)]
  pub fn sym(& self) -> & Sym { & self.sym }
  /** Signature of the state. */
  #[inline(always)]
  pub fn args(& self) -> & [(Sym, Type)] { self.args.args() }
}
impl fmt::Display for State {
  fn fmt(& self, fmt: & mut fmt::Formatter) -> fmt::Result {
    write!(fmt, "{}: {}", self.sym, self.args)
  }
}

/** An uninterpreted function declaration. */
#[derive(Debug,Clone)]
pub struct FunDec {
  /** Identifier of the function. */
  sym: Sym,
  /** Signature of the function. */
  sig: Sig,
  /** Return type of the function. */
  typ: Type,
}
impl FunDec {
  /** Creates a new uninterpreted function declaration. */
  #[inline(always)]
  pub fn mk(sym: Sym, sig: Sig, typ: Type) -> Self {
    FunDec { sym: sym, sig: sig, typ: typ }
  }
  /** Identifier of the function. */
  #[inline(always)]
  pub fn sym(& self) -> & Sym { & self.sym }
  /** Signature of the function. */
  #[inline(always)]
  pub fn sig(& self) -> & [Type] { & self.sig.types() }
  /** Return type of the function. */
  #[inline(always)]
  pub fn typ(& self) -> & Type { & self.typ }
}
impl fmt::Display for FunDec {
  fn fmt(& self, fmt: & mut fmt::Formatter) -> fmt::Result {
    write!(fmt, "{}{} -> {}", self.sym, self.sig, self.typ)
  }
}

/** A body, *i.e.* the result of the parsing of a term. */
#[derive(Debug,Clone)]
pub struct Body {
  /** Parse result. Contains the term. */
  body: StsResult,
}
impl Body {
  /** Creates a new body. */
  #[inline(always)]
  pub fn mk(body: StsResult) -> Self {
    Body { body: body }
  }
  /** Underlying parse result. Contains the term. */
  #[inline(always)]
  pub fn body(& self) -> & StsResult { & self.body }
}
impl fmt::Display for Body {
  fn fmt(& self, fmt: & mut fmt::Formatter) -> fmt::Result {
    write!(fmt, "{}", self.body)
  }
}

/** A function definition. */
#[derive(Debug,Clone)]
pub struct FunDef {
  /** Identifier of the function. */
  sym: Sym,
  /** Formal arguments of the function. */
  args: Args,
  /** Return type of the function. */
  typ: Type,
  /** Body of the function. */
  body: Body,
}
impl FunDef {
  /** Creates a new function declaration. */
  #[inline(always)]
  pub fn mk(sym: Sym, args: Args, typ: Type, body: Body) -> Self {
    FunDef { sym: sym, args: args, typ: typ, body: body }
  }
  /** Identifier of the function. */
  #[inline(always)]
  pub fn sym(& self) -> & Sym { & self.sym }
  /** Formal arguments of the function. */
  #[inline(always)]
  pub fn args(& self) -> & [(Sym, Type)] { & self.args.args() }
  /** Return type of the function. */
  #[inline(always)]
  pub fn typ(& self) -> & Type { & self.typ }
  /** Body of the function. */
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

/** A predicate definition. */
#[derive(Debug,Clone)]
pub struct Pred {
  /** Identifier of the predicate. */
  sym: Sym,
  /** State of the predicate. */
  state: Sym,
  /** Body of the predicate. */
  body: Body,
}
impl Pred {
  /** Creates a new predicate. */
  #[inline(always)]
  pub fn mk(sym: Sym, state: Sym, body: Body) -> Self {
    Pred { sym: sym, state: state, body: body }
  }
  /** Identifier of the predicate. */
  #[inline(always)]
  pub fn sym(& self) -> & Sym { & self.sym }
  /** State of the predicate. */
  #[inline(always)]
  pub fn state(& self) -> & Sym { & self.state }
  /** Body of the predicate. */
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

/** Init predicate definition. */
#[derive(Debug,Clone)]
pub struct Init {
  /** Identifier of the predicate. */
  sym: Sym,
  /** State of the predicate. */
  state: Sym,
  /** Body of the predicate. */
  body: Body,
}
impl Init {
  /** Creates a new init predicate. */
  #[inline(always)]
  pub fn mk(sym: Sym, state: Sym, body: Body) -> Self {
    Init { sym: sym, state: state, body: body }
  }
  /** Identifier of the predicate. */
  #[inline(always)]
  pub fn sym(& self) -> & Sym { & self.sym }
  /** State of the predicate. */
  #[inline(always)]
  pub fn state(& self) -> & Sym { & self.state }
  /** Body of the predicate. */
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

/** Transition predicate definition. */
#[derive(Debug,Clone)]
pub struct Trans {
  /** Identifier of the predicate. */
  sym: Sym,
  /** State of the predicate. */
  state: Sym,
  /** Body of the predicate. */
  body: Body,
}
impl Trans {
  /** Creates a new transition predicate. */
  #[inline(always)]
  pub fn mk(sym: Sym, state: Sym, body: Body) -> Self {
    Trans { sym: sym, state: state, body: body }
  }
  /** Identifier of the predicate. */
  #[inline(always)]
  pub fn sym(& self) -> & Sym { & self.sym }
  /** State of the predicate. */
  #[inline(always)]
  pub fn state(& self) -> & Sym { & self.state }
  /** Body of the predicate. */
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

/** System declaration. */
#[derive(Debug,Clone)]
pub struct Sys {
  /** Identifier of the system. */
  sym: Sym,
  /** State of the system. */
  state: Sym,
  /** Identifier of the init predicate of the system. */
  init: Sym,
  /** Identifier of the transition predicate of the system. */
  trans: Sym,
}
impl Sys {
  /** Creates a new system. */
  #[inline(always)]
  pub fn mk(sym: Sym, state: Sym, init: Sym, trans: Sym) -> Self {
    Sys { sym: sym, state: state, init: init, trans: trans }
  }
  /** Identifier of the system. */
  #[inline(always)]
  pub fn sym(& self) -> & Sym { & self.sym }
  /** State of the system. */
  #[inline(always)]
  pub fn state(& self) -> & Sym { & self.state }
  /** Identifier of the init predicate of the system. */
  #[inline(always)]
  pub fn init(& self) -> & Sym { & self.init }
  /** Identifier of the transition predicate of the system. */
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

/** Union type for declarations/definitions. */
#[derive(Debug,Clone)]
pub enum Item {
  /** Wraps a state. */
  St(State),
  /** Wraps an uninterpreted function. */
  FDc(FunDec),
  /** Wraps a function. */
  FDf(FunDef),
  /** Wraps a predicate. */
  P(Pred),
  /** Wraps an initial predicate. */
  I(Init),
  /** Wraps a transition predicate. */
  T(Trans),
  /** Wraps a system. */
  S(Sys),
}
impl Item {
  /** The identifier of an item. */
  pub fn sym(& self) -> & Sym {
    use self::Item::* ;
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
  /** A string representation of the kind of item wrapped. */
  pub fn desc(& self) -> & 'static str {
    use self::Item::* ;
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
  /** The state of the item wrapped, if any. */
  pub fn state(& self) -> Option<& Sym> {
    use self::Item::* ;
    match * self {
      P(ref e) => Some( e.state() ),
      I(ref e) => Some( e.state() ),
      T(ref e) => Some( e.state() ),
      S(ref e) => Some( e.state() ),
      _ => None,
    }
  }
}

/** Wraps an (uninterpreted) function. */
pub enum Callable {
  /** Wraps an uninterpreted function. */
  Dec(FunDec),
  /** Wraps a function. */
  Def(FunDef),
}
impl Callable {
  /** The symbol of a function. */
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