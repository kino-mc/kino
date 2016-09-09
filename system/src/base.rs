// Copyright 2015 Adrien Champion. See the COPYRIGHT file at the top-level
// directory of this distribution.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use std::fmt ;
use std::hash::{ Hash, Hasher } ;
use std::cmp::{ PartialEq, Eq } ;
use std::iter::Iterator ;
use std::collections::HashSet ;

use term::{
  Sym, Var, Type, Term, STerm, STermSet
} ;
use term::real_term::Cst ;

use Cex ;

/// Set of callables.
#[derive(Debug,Clone,PartialEq,Eq)]
pub struct CallSet {
  calls: Vec<::Callable>
}
impl CallSet {
  /// Creates an empty call set.
  pub fn empty() -> Self { CallSet { calls: vec![] } }
  /// Returns `true` iff the set is empty.
  pub fn is_empty(& self) -> bool {
    self.calls.is_empty()
  }
  /// Returns `true` iff the set contains the element.
  pub fn contains(& self, e: & ::Callable) -> bool {
    self.calls.contains(e)
  }
  /// Inserts a call into a call set, recursively going down the subcalls.
  pub fn insert(& mut self, fun: ::Callable) {
    // println!("\n\n|===| insert") ;

    let mut stack = vec![ vec![fun] ] ;
    let mut cpt = 0 ;
    loop {
      cpt += 1 ;
      if cpt >= 10 { panic!("aaa") } ;
      // println!(
      //   "\nstack:{}",
      //   stack.iter().fold(
      //     String::new(),
      //     |s, calls| format!(
      //       "{}\n {}", s,
      //       calls.iter().fold(
      //         String::new(),
      //         |s, call| format!("{} {}", s, call.sym())
      //       )
      //     )
      //   )
      // ) ;
      if let Some(mut calls) = stack.pop() {
        if let Some(call) = calls.pop() {
          // println!(
          //   "calls: ({}){}",
          //   self.calls.len(),
          //   self.calls.iter().fold(
          //     "".to_string(),
          //     |s, call| format!("{}\n  {}", s, call.sym())
          //   )
          // ) ;
          // println!("call: {}", call.sym()) ;
          // Skipping if already known.
          if ! self.calls.contains(& call) {
            // println!("  new call") ;
            if call.calls().is_empty() {
              // println!("  no subcall") ;
              // No sub call.
              self.calls.push( call.clone() ) ;
              // println!("  done updating calls ({})", self.calls.len()) ;
            } else {
              // println!("  {} subcall(s)", call.calls().len()) ;
              // Call has subcalls.
              let vec = {
                let sub_calls = call.calls() ;
                sub_calls.iter().fold(
                  Vec::with_capacity(sub_calls.len()),
                  |mut v, sc| {
                    if ! self.calls.contains(sc) { v.push(sc.clone()) } ;
                    v
                  }
                )
              } ;
              if ! vec.is_empty() {
                // Some calls are unknown.
                calls.push(call) ;
                stack.push(calls) ;
                stack.push(vec) ;
              } else {
                // No unknown subcalls.
                stack.push(calls) ;
                self.calls.push(call.clone())
              }
            }
          } else {
            // println!("  known call")
          }
        }
      } else { break }
    }
  }
  /// The calls in the set, ordered by topological order.
  pub fn get(& self) -> & [::Callable] { & self.calls }
}


/// A signature, a list of types. Used only in `Uf`.
#[derive(Debug,Clone)]
pub struct Sig {
  /// Types of the signature.
  types: Vec<Type>,
}
impl Sig {
  /// Creates a new signature.
  #[inline(always)]
  pub fn mk(types: Vec<Type>) -> Self {
    Sig { types: types }
  }
  /// The types of a signature.
  #[inline(always)]
  pub fn types(& self) -> & [Type] { & self.types }
}
impl fmt::Display for Sig {
  fn fmt(& self, fmt: & mut fmt::Formatter) -> fmt::Result {
    let mut iter = self.types.iter() ;
    if let Some(ref t) = iter.next() {
      try!( write!(fmt, "{}", t) ) ;
      for t in iter {
        try!( write!(fmt, " {}", t) )
      }
    } ;
    Ok(())
  }
}

/// A list of typed formal parameters.
#[derive(Debug,Clone)]
pub struct Args {
  /// The symbol/type pair list.
  args: Vec<(Sym, Type)>,
}
impl Args {
  /// Creates a new argument list.
  #[inline(always)]
  pub fn mk(args: Vec<(Sym, Type)>) -> Self {
    Args { args: args }
  }
  /// The formal parameters.
  #[inline(always)]
  pub fn args(& self) -> & [(Sym, Type)] { & self.args }
  /// Number of paramaters.
  #[inline(always)]
  pub fn len(& self) -> usize { self.args.len() }
  /// Returns true iff a symbol is a list of arguments.
  pub fn contains(& self, sym: & Sym) -> bool {
    for & (ref arg, _) in self.args() {
      if sym == arg { return true }
    } ;
    false
  }
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

/// An uninterpreted function.
#[derive(Debug,Clone)]
pub struct Uf {
  /// Identifier of the function.
  sym: Sym,
  /// Signature of the function.
  sig: Sig,
  /// Return type of the function.
  typ: Type,
}
impl Uf {
  /// Creates a new uninterpreted function.
  #[inline(always)]
  pub fn mk(sym: Sym, sig: Sig, typ: Type) -> Self {
    Uf { sym: sym, sig: sig, typ: typ }
  }
  /// Identifier of a function.
  #[inline(always)]
  pub fn sym(& self) -> & Sym { & self.sym }
  /// Signature of a function.
  #[inline(always)]
  pub fn sig(& self) -> & [Type] { & self.sig.types() }
  /// Return type of a function.
  #[inline(always)]
  pub fn typ(& self) -> & Type { & self.typ }
}
impl fmt::Display for Uf {
  fn fmt(& self, fmt: & mut fmt::Formatter) -> fmt::Result {
    write!(fmt, "{} ({}) -> {}", self.sym, self.sig, self.typ)
  }
}
impl PartialEq for Uf {
  fn eq(& self, other: & Uf) -> bool {
    self.sym == other.sym
  }
}
impl Eq for Uf {}
impl Hash for Uf {
  fn hash<H: Hasher>(& self, state: & mut H) {
    self.sym.hash(state)
  }
}

/// A function (actually a macro in SMT-LIB).
#[derive(Debug,Clone)]
pub struct Fun {
  /// Identifier of the function.
  sym: Sym,
  /// Formal arguments of the function.
  args: Args,
  /// Return type of the function.
  typ: Type,
  /// Body of the function.
  body: Term,
  /// Callables used by this function **recursively**.
  calls: CallSet,
}
impl Fun {
  /// Creates a new function.
  #[inline(always)]
  pub fn mk(
    sym: Sym, args: Args, typ: Type, body: Term, calls: CallSet
  ) -> Self {
    Fun { sym: sym, args: args, typ: typ, body: body, calls: calls }
  }
  /// Identifier of a function.
  #[inline(always)]
  pub fn sym(& self) -> & Sym { & self.sym }
  /// Formal arguments of a function.
  #[inline(always)]
  pub fn args(& self) -> & [(Sym, Type)] { & self.args.args() }
  /// Return type of a function.
  #[inline(always)]
  pub fn typ(& self) -> & Type { & self.typ }
  /// Body of a function.
  #[inline(always)]
  pub fn body(& self) -> & Term { & self.body }
  /// Calls of a function.
  #[inline(always)]
  pub fn calls(& self) -> & CallSet { & self.calls }
}
impl fmt::Display for Fun {
  fn fmt(& self, fmt: & mut fmt::Formatter) -> fmt::Result {
    write!(
      fmt, "{} ({}) -> {} {{ {} }}", self.sym, self.args, self.typ, self.body
    )
  }
}
impl PartialEq for Fun {
  fn eq(& self, other: & Fun) -> bool {
    self.sym == other.sym
  }
}
impl Eq for Fun {}
impl Hash for Fun {
  fn hash<H: Hasher>(& self, state: & mut H) {
    self.sym.hash(state)
  }
}

/// Wraps an (uninterpreted) function.
#[derive(Debug,Clone,PartialEq,Eq,Hash)]
pub enum Callable {
  /// Wraps an uninterpreted function.
  Dec(Uf),
  /// Wraps a function.
  Def(Fun),
}
impl Callable {
  /// The calls made by the function if any.
  #[inline(always)]
  pub fn calls(& self) -> & [::Callable] {
    match * self {
      Callable::Dec(_) => & [],
      Callable::Def(ref fun) => fun.calls.get(),
    }
  }
  /// The symbol of a function.
  pub fn sym(& self) -> & Sym {
    match * self {
      Callable::Def(ref f) => f.sym(),
      Callable::Dec(ref f) => f.sym(),
    }
  }
  /// Returns the output type if the input signature type checks.
  pub fn type_check(& self, sig: & [ Type ]) -> Result<Type, (usize, String)> {
    // use std::iter::Zip ;
    let mut cpt = 0 ;
    let typ = match * self {
      Callable::Dec(ref fun) => {
        for (
          type_formal, type_actual
        ) in fun.sig().iter().zip(sig.iter()) {
          if type_formal != type_actual {
            return Err( (
              cpt,
              format!(
                "parameter {} of the application of UF {}:\n  \
                  expected {}, got {}",
                cpt + 1, self.sym(), type_formal, type_actual
              )
            ) )
          } ;
          cpt = cpt + 1 ;
        } ;
        fun.typ().clone()
      },
      Callable::Def(ref fun) => {
        for (
          & (ref sym, ref type_formal), ref type_actual
        ) in fun.args().iter().zip(sig.iter()) {
          if type_formal != * type_actual {
            return Err( (
              cpt,
              format!(
                "parameter {} of function {}: expected {}, got {}",
                sym, self.sym(), type_formal, type_actual
              )
            ) )
          } ;
          cpt = cpt + 1 ;
        } ;
        fun.typ().clone()
      },
    } ;
    Ok( typ )
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

/// Status of a property.
pub enum PropStatus {
  /// Unknown.
  Unknown,
  /// True up to k transitions from the initial states.
  KTrue(usize),
  /// Falsified, with a cex.
  Falsified(Cex),
  /// K-inductive invariant without minimization.
  Invariant(usize),
  /// Minimized k-inductive invariant with lemmas.
  MinInvariant(usize, STermSet),
}
impl fmt::Display for PropStatus {
  fn fmt(& self, fmt: & mut fmt::Formatter) -> fmt::Result {
    use self::PropStatus::* ;
    match * self {
      Unknown => write!(fmt, "unknown"),
      KTrue(ref k) => write!(fmt, "true up to {} transitions", k),
      Falsified(ref model) => write!(fmt, "falsified at {}", model.len()),
      Invariant(ref k) => write!(fmt, "{}-inductive", k),
      MinInvariant(ref k, ref invs) => write!(
        fmt, "{}-inductive with {} lemmas (minimized)", k, invs.len()
      ),
    }
  }
}

/// A property.
#[derive(Debug,Clone)]
pub struct Prop {
  /// Identifier of the property.
  sym: Sym,
  /// System the property is over.
  sys: ::Sys,
  /// Body of the property.
  body: STerm,
  /// Calls in the property.
  calls: CallSet,
}
impl Prop {
  /// Creates a new property.
  #[inline(always)]
  pub fn mk(sym: Sym, sys: ::Sys, body: STerm, calls: CallSet) -> Self {
    Prop { sym: sym, sys: sys, body: body, calls: calls }
  }
  /// Identifier of a property.
  #[inline(always)]
  pub fn sym(& self) -> & Sym { & self.sym }
  /// System a property ranges over.
  #[inline(always)]
  pub fn sys(& self) -> & ::Sys { & self.sys }
  /// Body of a property.
  #[inline(always)]
  pub fn body(& self) -> & STerm { & self.body }
  /// Calls of a property.
  #[inline(always)]
  pub fn calls(& self) -> & CallSet { & self.calls }
}
impl fmt::Display for Prop {
  fn fmt(& self, fmt: & mut fmt::Formatter) -> fmt::Result {
    write!(
      fmt, "{} ({}) {{ {} }}", self.sym, self.sys.sym(), self.body
    )
  }
}
impl PartialEq for Prop {
  fn eq(& self, other: & Prop) -> bool {
    self.sym == other.sym
  }
}
impl Eq for Prop {}
impl Hash for Prop {
  fn hash<H: Hasher>(& self, state: & mut H) {
    self.sym.hash(state)
  }
}

/// A transition system.
#[derive(Debug,Clone)]
pub struct Sys {
  /// Identifier of the system.
  sym: Sym,
  /// State of the system.
  state: Args,
  /// Local variables of the system.
  locals: Vec<(Sym, Type, Term)>,
  /// Identifier of the init predicate of the system.
  init: (Sym, Vec<(Var, Type)>, Term, Term),
  /// Identifier of the transition relation of the system.
  trans: (Sym, Vec<(Var, Type)>, Term, Term),
  /// Calls of the system.
  subsys: Vec<(::Sys, Vec<Term>)>,
  /// Callables used by this system **recursively**.
  calls: CallSet,
}
impl Sys {
  /// Creates a new system.
  #[inline(always)]
  pub fn mk(
    sym: Sym, state: Args, locals: Vec<(Sym, Type, Term)>,
    init: (Sym, Vec<(Var, Type)>, Term, Term),
    trans: (Sym, Vec<(Var, Type)>, Term, Term),
    subsys: Vec<(::Sys, Vec<Term>)>,
    calls: CallSet,
  ) -> Self {
    Sys {
      sym: sym, state: state, locals: locals,
      init: init, trans: trans,
      subsys: subsys, calls: calls,
    }
  }
  /// Identifier of a system.
  #[inline(always)]
  pub fn sym(& self) -> & Sym { & self.sym }
  /// State of a system.
  #[inline(always)]
  pub fn state(& self) -> & Args { & self.state }
  /// Locals variables of a system.
  #[inline(always)]
  pub fn locals(& self) -> & [ (Sym, Type, Term) ] { & self.locals }
  /// Init predicate of a system.
  #[inline(always)]
  pub fn init(& self) -> & (Sym, Vec<(Var, Type)>, Term, Term) {
    & self.init
  }
  /// Init term.
  #[inline(always)]
  pub fn init_term(& self) -> & Term { & self.init.3 }
  /// Transition relation of a system.
  #[inline(always)]
  pub fn trans(& self) -> & (Sym, Vec<(Var, Type)>, Term, Term) {
    & self.trans
  }
  /// Trans term.
  #[inline(always)]
  pub fn trans_term(& self) -> & Term { & self.trans.3 }
  /// Sub-systems of a system.
  #[inline(always)]
  pub fn subsys(& self) -> & [ (::Sys, Vec<Term>) ] { & self.subsys }
  /// Symbols of the sub-systems of a system, has a hash set.
  #[inline]
  pub fn subsys_syms(& self) -> HashSet<Sym> {
    let mut set = HashSet::with_capacity( self.subsys.len() ) ;
    for & (ref sub, _) in self.subsys.iter() {
      set.insert(sub.sym().clone()) ; ()
    }
    set.shrink_to_fit() ;
    set
  }
  /// Calls of a system.
  #[inline(always)]
  pub fn calls(& self) -> & CallSet { & self.calls }

  /// Default value for a symbol.
  pub fn default_value(& self, sym: & Sym) -> Result<Cst, String> {
    for & (ref sym, ref typ) in self.state().args() {
      if sym == sym {
        return Ok( typ.default() )
      }
    }
    Err( format!("[sys] unknown symbol {}", sym) )
  }

  /// String representation of a system as lines.
  pub fn lines(& self) -> String {
    let mut s = format!(
      "{} ({})\n  init:  {}\n  trans: {}",
      self.sym, self.state, self.init.2, self.trans.2
    ) ;
    if ! self.subsys.is_empty() {
      s = format!("{}\n  sub-systems:", s) ;
      for & (ref sub_sym, ref params) in self.subsys.iter() {
        s = format!("{}\n    {} (", s, sub_sym.sym()) ;
        for param in params {
          s = format!("{}\n      {}", s, param) ;
        } ;
        s = format!("{}\n    )", s) ;
      } ;
    } ;
    if ! self.calls.is_empty() {
      s = format!("{}\n  calls:", s) ;
      for callable in self.calls.get() {
        s = format!("{}\n    {}", s, callable.sym()) ;
      } ;
    } ;
    s
  }
}
impl PartialEq<Sym> for Sys {
  fn eq(& self, rhs: & Sym) -> bool {
    self.sym == * rhs
  }
}
impl fmt::Display for Sys {
  fn fmt(& self, fmt: & mut fmt::Formatter) -> fmt::Result {
    write!(
      fmt, "{} ({}) {{ {} -> {} }}",
      self.sym, self.state, self.init.2, self.trans.2
    )
  }
}



