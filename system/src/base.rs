// Copyright 2015 Adrien Champion. See the COPYRIGHT file at the top-level
// directory of this distribution.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use std::fmt ;
use std::rc::Rc ;
use std::collections::HashSet ;

use term::{ Sym, Type, Term } ;

/** A signature, a list of types. Used only in `Uf`. */
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
  /** The types of a signature. */
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

/** A list of typed formal parameters. */
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
  /** The formal parameters. */
  #[inline(always)]
  pub fn args(& self) -> & [(Sym, Type)] { & self.args }
}
impl fmt::Display for Args {
  fn fmt(& self, fmt: & mut fmt::Formatter) -> fmt::Result {
    let mut iter = self.args.iter() ;
    if let Some( & (ref s, ref t) ) = iter.next() {
      try!( write!(fmt, "({} {})", s, t) ) ;
      for & ( ref s, ref t) in iter {
        try!( write!(fmt, " ({} {})", s, t) )
      }
    } ;
    Ok(())
  }
}

// pub struct StatelessDep {
//   funs: HashSet<Sym>,
// }
// impl StatelessDep {
//   pub fn mk(funs: HashSet<Sym>) -> Self {
//     StatelessDep { funs: funs }
//   }
// }

// pub struct StatefulDep {
//   funs: HashSet<Sym>,
//   inits: HashSet<Sym>,
//   transs: HashSet<Sym>,
// }
// impl StatefulDep {
//   pub fn mk(
//     funs: HashSet<Sym>, inits: HashSet<Sym>, transs: HashSet<Sym>
//   ) -> Self {
//     StatefulDep { funs: funs, inits: inits, transs: transs }
//   }
// }

/** An uninterpreted function. */
#[derive(Debug,Clone)]
pub struct Uf {
  /** Identifier of the function. */
  sym: Sym,
  /** Signature of the function. */
  sig: Sig,
  /** Return type of the function. */
  typ: Type,
}
impl Uf {
  /** Creates a new uninterpreted function. */
  #[inline(always)]
  pub fn mk(sym: Sym, sig: Sig, typ: Type) -> Self {
    Uf { sym: sym, sig: sig, typ: typ }
  }
  /** Identifier of a function. */
  #[inline(always)]
  pub fn sym(& self) -> & Sym { & self.sym }
  /** Signature of a function. */
  #[inline(always)]
  pub fn sig(& self) -> & [Type] { & self.sig.types() }
  /** Return type of a function. */
  #[inline(always)]
  pub fn typ(& self) -> & Type { & self.typ }
}
impl fmt::Display for Uf {
  fn fmt(& self, fmt: & mut fmt::Formatter) -> fmt::Result {
    write!(fmt, "{} ({}) -> {}", self.sym, self.sig, self.typ)
  }
}

/** A function (actually as a macro in SMT-LIB). */
#[derive(Debug,Clone)]
pub struct Fun {
  /** Identifier of the function. */
  sym: Sym,
  /** Formal arguments of the function. */
  args: Args,
  /** Return type of the function. */
  typ: Type,
  /** Body of the function. */
  body: Term,
}
impl Fun {
  /** Creates a new function. */
  #[inline(always)]
  pub fn mk(sym: Sym, args: Args, typ: Type, body: Term) -> Self {
    Fun { sym: sym, args: args, typ: typ, body: body }
  }
  /** Identifier of a function. */
  #[inline(always)]
  pub fn sym(& self) -> & Sym { & self.sym }
  /** Formal arguments of a function. */
  #[inline(always)]
  pub fn args(& self) -> & [(Sym, Type)] { & self.args.args() }
  /** Return type of a function. */
  #[inline(always)]
  pub fn typ(& self) -> & Type { & self.typ }
  /** Body of a function. */
  #[inline(always)]
  pub fn body(& self) -> & Term { & self.body }
}
impl fmt::Display for Fun {
  fn fmt(& self, fmt: & mut fmt::Formatter) -> fmt::Result {
    write!(
      fmt, "{} ({}) -> {} {{ {} }}", self.sym, self.args, self.typ, self.body
    )
  }
}

/** A property. */
#[derive(Debug,Clone)]
pub struct Prop {
  /** Identifier of the property. */
  sym: Sym,
  /** System the property is over. */
  sys: Rc<Sys>,
  /** Body of the property. */
  body: Term,
}
impl Prop {
  /** Creates a new property. */
  #[inline(always)]
  pub fn mk(sym: Sym, sys: Rc<Sys>, body: Term) -> Self {
    Prop { sym: sym, sys: sys, body: body }
  }
  /** Identifier of a property. */
  #[inline(always)]
  pub fn sym(& self) -> & Sym { & self.sym }
  /** System a property ranges over. */
  #[inline(always)]
  pub fn sys(& self) -> & Rc<Sys> { & self.sys }
  /** Body of a property. */
  #[inline(always)]
  pub fn body(& self) -> & Term { & self.body }
}
impl fmt::Display for Prop {
  fn fmt(& self, fmt: & mut fmt::Formatter) -> fmt::Result {
    write!(
      fmt, "{} ({}) {{ {} }}", self.sym, self.sys.sym(), self.body
    )
  }
}

/** A transition system. */
#[derive(Debug,Clone)]
pub struct Sys {
  /** Identifier of the system. */
  sym: Sym,
  /** State of the system. */
  state: Args,
  /** Local variables of the system. */
  locals: Vec<(Sym, Type, Term)>,
  /** Identifier of the init predicate of the system. */
  init: Term,
  /** Identifier of the transition relation of the system. */
  trans: Term,
  /** Calls of the system. */
  calls: Vec<(Rc<Sys>, Vec<Term>)>
}
impl Sys {
  /** Creates a new system. */
  #[inline(always)]
  pub fn mk(
    sym: Sym, state: Args, locals: Vec<(Sym, Type, Term)>,
    init: Term, trans: Term,
    calls: Vec<(Rc<Sys>, Vec<Term>)>
  ) -> Self {
    Sys {
      sym: sym, state: state, locals: locals,
      init: init, trans: trans, calls: calls
    }
  }
  /** Identifier of a system. */
  #[inline(always)]
  pub fn sym(& self) -> & Sym { & self.sym }
  /** State of a system. */
  #[inline(always)]
  pub fn state(& self) -> & Args { & self.state }
  /** Locals variables of a system. */
  #[inline(always)]
  pub fn locals(& self) -> & [ (Sym, Type, Term) ] { & self.locals }
  /** Init predicate of a system. */
  #[inline(always)]
  pub fn init(& self) -> & Term { & self.init }
  /** Calls of a system. */
  #[inline(always)]
  pub fn calls(& self) -> & [ (Rc<Sys>, Vec<Term>) ] { & self.calls }
  /** Transition relation of a system. */
  #[inline(always)]
  pub fn trans(& self) -> & Term { & self.trans }
  /** String representation of a system as lines. */
  pub fn lines(& self) -> String {
    let mut s = format!(
      "{} ({})\n  init:  {}\n  trans: {}",
      self.sym, self.state, self.init, self.trans
    ) ;
    if ! self.calls.is_empty() {
      s = format!("{}\n  calls:", s) ;
      for & (ref sub_sym, ref params) in self.calls.iter() {
        s = format!("{}\n    {} (", s, sub_sym.sym()) ;
        for param in params {
          s = format!("{}\n      {}", s, param) ;
        } ;
        s = format!("{}\n    )", s) ;
      } ;
    } ;
    s
  }
}
impl fmt::Display for Sys {
  fn fmt(& self, fmt: & mut fmt::Formatter) -> fmt::Result {
    write!(
      fmt, "{} ({}) {{ {} -> {} }}",
      self.sym, self.state, self.init, self.trans
    )
  }
}

/** Wraps an (uninterpreted) function. */
pub enum Callable {
  /** Wraps an uninterpreted function. */
  Dec(Uf),
  /** Wraps a function. */
  Def(Fun),
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