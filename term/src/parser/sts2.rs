// Copyright 2015 Adrien Champion. See the COPYRIGHT file at the top-level
// directory of this distribution.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

/*! Parsers for the `sts` format. */

use std::str ;
use std::collections::HashSet ;
use std::fmt ;

use nom::{ IResult } ;

use base::State ;
use typ::Type ;
use cst::Cst ;
use sym::Sym ;
use var::{ VarMaker, Var } ;
use term::{ Term, Operator } ;
use factory::Factory ;

use super::{
  type_parser,
  space_comment,
  simple_symbol_head, simple_symbol_tail,
  operator_parser,
  quantifier_parser, Quantifier
} ;

/** Result of STS parsing. */
#[derive(Clone,Debug)]
pub struct TermAndDep {
  /** The term parsed. */
  pub term: Term,
  /** The function symbol applications in the term. */
  pub apps: HashSet<Sym>,
  /** The variables in the term. */
  pub vars: HashSet<Var>,
  /** Types found in the term.
  Does **not** include the types of variables. */
  pub types: HashSet<Type>,
  /** Whether the term is linear. */
  pub linear: bool,
  /** Whether the term is quantifier-free. */
  pub qf: bool,
}
impl fmt::Display for TermAndDep {
  fn fmt(& self, fmt: & mut fmt::Formatter) -> fmt::Result {
    self.term.fmt(fmt)
  }
}
impl TermAndDep {
  pub fn var(factory: & Factory, var: Var) -> Self {
    let term = factory.mk_var(var.clone()) ;
    let mut vars = HashSet::new() ;
    vars.insert(var) ;
    TermAndDep {
      term: term,
      apps: HashSet::new(),
      vars: vars,
      types: HashSet::new(),
      linear: true,
      qf: true,
    }
  }
  pub fn cst(factory: & Factory, cst: Cst) -> Self {
    use term::CstMaker ;
    let mut types = HashSet::new() ;
    types.insert( cst.get().typ() ) ;
    let term = factory.cst(cst) ;
    TermAndDep {
      term: term,
      apps: HashSet::new(),
      vars: HashSet::new(),
      types: types,
      linear: true,
      qf: true,
    }
  }

  #[inline(always)]
  fn merge(kids: Vec<TermAndDep>) -> (
    Vec<Term>,
    HashSet<Sym>,
    HashSet<Var>,
    HashSet<Type>,
    usize,
    bool,
    bool,
  ) {
    use std::iter::Extend ;
    let mut subs = vec![] ;
    let mut apps = HashSet::new() ;
    let mut vars = HashSet::new() ;
    let mut types = HashSet::new() ;
    let mut linear = true ;
    let mut qf = true ;
    let mut kids_with_vars = 0 ;
    for kid in kids.into_iter() {
      subs.push( kid.term ) ;
      apps.extend( kid.apps ) ;
      if ! kid.vars.is_empty() {
        kids_with_vars = kids_with_vars + 1
      } ;
      vars.extend( kid.vars ) ;
      types.extend( kid.types ) ;
      if ! kid.linear { linear = false } ;
      if ! kid.qf { qf = false } ;
    }
    ( subs, apps, vars, types, kids_with_vars, linear, qf )
  }

  pub fn op(factory: & Factory, op: Operator, kids: Vec<TermAndDep>) -> Self {
    use term::Operator::* ;
    use term::OpMaker ;
    let (
      subs, apps, vars, types, kids_with_vars, linear, qf
    ) = Self::merge(kids) ;
    let linear = linear && match op {
      Mul | Div => kids_with_vars >= 2,
      _ => false,
    } ;
    let term = factory.op(op, subs) ;
    TermAndDep {
      term: term,
      apps: apps,
      vars: vars,
      types: types,
      linear: linear,
      qf: qf,
    }
  }

  pub fn app(factory: & Factory, sym: Sym, kids: Vec<TermAndDep>) -> Self {
    use term::AppMaker ;
    let (
      subs, mut apps, vars, types, kids_with_vars, linear, qf
    ) = Self::merge(kids) ;
    let linear = linear && kids_with_vars >= 2 ;
    apps.insert(sym.clone()) ;
    let term = factory.app(sym, subs) ;
    TermAndDep {
      term: term,
      apps: apps,
      vars: vars,
      types: types,
      linear: linear,
      qf: qf,
    }
  }

  fn quantifier(
    factory: & Factory, bindings: Vec<(Sym, Type)>, kid: TermAndDep, univ: bool
  ) -> Self {
    use term::BindMaker ;
    let term = kid.term ;
    let apps = kid.apps ;
    let mut vars = kid.vars ;
    let mut types = kid.types ;
    let linear = kid.linear ;
    let mut binds = vec![] ;
    for (sym, typ) in bindings.into_iter() {
      let var = factory.var_consign().var(sym.clone()) ;
      let was_there = vars.remove(& var) ;
      if was_there {
        binds.push( (sym, typ) ) ;
        types.insert(typ) ;
        ()
      } ;
    } ;
    let term = if univ {
      factory.forall(binds, term)
    } else {
      factory.exists(binds, term)
    } ;
    TermAndDep {
      term: term,
      apps: apps,
      vars: vars,
      types: types,
      linear: linear,
      qf: true,
    }
  }

  pub fn forall(
    factory: & Factory, bindings: Vec<(Sym, Type)>, kid: TermAndDep
  ) -> Self {
    Self::quantifier(factory, bindings, kid, true)
  }

  pub fn exists(
    factory: & Factory, bindings: Vec<(Sym, Type)>, kid: TermAndDep
  ) -> Self {
    Self::quantifier(factory, bindings, kid, true)
  }

  pub fn let_b(
    factory: & Factory, bindings: Vec<(Sym, TermAndDep)>, kid: TermAndDep
  ) -> Self {
    use term::BindMaker ;
    use std::iter::Extend ;
    let term = kid.term ;
    let mut apps = kid.apps ;
    let mut vars = kid.vars ;
    let mut types = kid.types ;
    let mut linear = kid.linear ;
    let mut qf = kid.qf ;
    let mut binds = vec![] ;
    let mut bind_vars = HashSet::new() ;
    for (sym, res) in bindings.into_iter() {
      let var = factory.var_consign().var(sym.clone()) ;
      let was_there = vars.remove(& var) ;
      if was_there {
        let term = res.term ;
        apps.extend(res.apps) ;
        bind_vars.extend(res.vars) ;
        types.extend(res.types) ;
        linear = linear && res.linear ;
        qf = qf && res.qf ;
        binds.push( (sym, term) ) ;
      } ;
    } ;
    vars.extend(bind_vars) ;
    let term = factory.let_b(binds, term) ;
    TermAndDep {
      term: term,
      apps: apps,
      vars: vars,
      types: types,
      linear: linear,
      qf: qf,
    }
  }
}

named!{ state<State>,
  alt!(
    map!( tag!("state"), |_| State::Curr ) |
    map!( tag!("next"), |_| State::Next  )
  )
}

named!{ pub id_parser<String>,
  alt!(
    // Simple symbol.
    chain!(
      head: simple_symbol_head ~
      tail: map!( simple_symbol_tail, str::from_utf8 ),
      || format!("{}{}", head, tail.unwrap())
    ) |
    // Quoted symbol.
    delimited!(
      char!('|'),
      chain!(
        head: none_of!("|\\@") ~
        sym: map!(
          is_not!("|\\"), str::from_utf8
        ),
        || format!("{}{}", head, sym.unwrap())
      ),
      char!('|')
    )
  )
}


pub fn var_parser<'a>(
  bytes: & 'a [u8], f: & Factory
) -> IResult<'a, & 'a [u8], TermAndDep> {
  use sym::SymMaker ;
  alt!(
    bytes,
    chain!(
      char!('(') ~
      opt!(space_comment) ~
      state: state ~
      space_comment ~
      sym: map!(
        id_parser, |s| f.sym(s)
      ) ~
      opt!(space_comment) ~
      char!(')'),
      || {
        let var = f.var_consign().svar(sym, state) ;
        TermAndDep::var(f, var)
      }
    ) |
    map!(
      id_parser, |s| {
        let var = f.var_consign().var( f.sym(s) ) ;
        TermAndDep::var(f, var)
      }
    )
  )
}

pub fn cst_parser<'a>(
  bytes: & 'a [u8], f: & Factory
) -> IResult<'a, & 'a [u8], TermAndDep> {
  use term::CstMaker ;
  map!(
    bytes,
    apply!( super::cst_parser, f.cst_consign() ),
    |cst| TermAndDep::cst(f, cst)
  )
}

pub fn op_parser<'a>(
  bytes: & 'a [u8], f: & Factory
) -> IResult<'a, & 'a [u8], TermAndDep> {
  use term::OpMaker ;
  chain!(
    bytes,
    char!('(') ~
    opt!(space_comment) ~
    op: operator_parser ~
    space_comment ~
    args: separated_list!(
      space_comment, apply!(term_parser, f)
    ) ~
    opt!(space_comment) ~
    char!(')'),
    || TermAndDep::op(f, op, args)
  )
}


pub fn quantified_parser<'a>(
  bytes: & 'a [u8], f: & Factory
) -> IResult<'a, & 'a [u8], TermAndDep> {
  use sym::SymMaker ;
  use term::BindMaker ;
  chain!(
    bytes,
    char!('(') ~
    opt!(space_comment) ~
    quantifier: quantifier_parser ~
    opt!(space_comment) ~
    char!('(') ~
    bindings: separated_list!(
      opt!(space_comment),
      delimited!(
        char!('('),
        chain!(
          opt!(space_comment) ~
          sym: map!(
            id_parser,
            |sym| f.sym(sym)
          ) ~
          space_comment ~
          ty: type_parser ~
          opt!(space_comment),
          || (sym, ty)
        ),
        char!(')')
      )
    ) ~
    opt!(space_comment) ~
    char!(')') ~
    opt!(space_comment) ~
    term: apply!(term_parser, f) ~
    opt!(space_comment) ~
    char!(')'),
    || match quantifier {
      Quantifier::Forall => TermAndDep::forall(f, bindings, term),
      Quantifier::Exists => TermAndDep::exists(f, bindings, term),
    }
  )
}

pub fn let_parser<'a>(
  bytes: & 'a [u8], f: & Factory
) -> IResult<'a, & 'a [u8], TermAndDep> {
  use sym::SymMaker ;
  use term::BindMaker ;
  chain!(
    bytes,
    char!('(') ~
    opt!(space_comment) ~
    tag!("let") ~
    opt!(space_comment) ~
    char!('(') ~
    bindings: separated_list!(
      opt!(space_comment),
      delimited!(
        char!('('),
        chain!(
          opt!(space_comment) ~
          sym: map!(
            id_parser,
            |sym| f.sym(sym)
          ) ~
          space_comment ~
          term: apply!(term_parser, f) ~
          opt!(space_comment),
          || (sym, term)
        ),
        char!(')')
      )
    ) ~
    opt!(space_comment) ~
    char!(')') ~
    opt!(space_comment) ~
    term: apply!(term_parser, f) ~
    opt!(space_comment) ~
    char!(')'),
    || TermAndDep::let_b(f, bindings, term)
  )
}

fn app_parser<'a>(
  bytes: & 'a [u8], f: & Factory
) -> IResult<'a, & 'a [u8], TermAndDep> {
  use sym::SymMaker ;
  use term::AppMaker ;
  chain!(
    bytes,
    char!('(') ~
    space_comment ~
    sym: id_parser ~
    space_comment ~
    args: separated_list!(
      space_comment, apply!(term_parser, f)
    ) ~
    opt!(space_comment) ~
    char!(')'),
    || {
      let sym = f.sym(sym) ;
      TermAndDep::app(f, sym, args )
    }
  )
}


pub fn term_parser<'a>(
  bytes: & 'a [u8], f: & Factory
) -> IResult<'a, & 'a [u8], TermAndDep> {
  alt!(
    bytes,
    apply!(cst_parser, f) |
    apply!(var_parser, f) |
    apply!(op_parser, f) |
    apply!(quantified_parser, f) |
    apply!(let_parser, f) |
    apply!(app_parser, f)
  )
}







#[cfg(test)]
macro_rules! try_parse_term {
  ($fun:expr, $factory:expr, $arg:expr, $e:expr) => (
    try_parse!($fun, $factory, $arg,
      (s, res) -> {
        assert_eq!(res, $e)
      }
    )
  ) ;
}


#[cfg(test)]
mod terms {
  use base::{ State, PrintSts2 } ;
  use sym::* ;
  use var::* ;
  use term::{ Operator, CstMaker, OpMaker, AppMaker } ;
  use factory::* ;
  use typ::* ;
  use std::str::FromStr ;

  #[test]
  fn cst() {
    use super::* ;
    let factory = Factory::mk() ;
    let res = factory.cst( Int::from_str("7").unwrap() ) ;
    try_parse_term!(
      term_parser, & factory,
      b"7",
      res
    ) ;
    let res = factory.cst(
      Rat::new(
        Int::from_str("5357").unwrap(),
        Int::from_str("2046").unwrap()
      )
    ) ;
    try_parse_term!(
      term_parser, & factory,
      b"(/ 5357 2046)",
      res
    ) ;
    let res = factory.cst( true ) ;
    try_parse_term!(
      term_parser, & factory,
      b"true",
      res
    ) ;
    let res = factory.cst( false ) ;
    try_parse_term!(
      term_parser, & factory,
      b"false",
      res
    ) ;
  }

  #[test]
  fn var() {
    use super::* ;
    let factory = Factory::mk() ;
    let res = factory.var( factory.sym("bla") ) ;
    try_parse_term!(
      term_parser, & factory,
      b"bla",
      res
    ) ;
    let res = factory.var( factory.sym("bly.bla") ) ;
    try_parse_term!(
      term_parser, & factory,
      b"bly.bla",
      res
    ) ;
    let res = factory.svar( factory.sym("bla"), State::Curr ) ;
    try_parse_term!(
      term_parser, & factory,
      b"(state bla)",
      res
    ) ;
    let res = factory.svar( factory.sym("bla"), State::Next ) ;
    try_parse_term!(
      term_parser, & factory,
      b"(next bla)",
      res
    ) ;
  }

  #[test]
  fn op() {
    use super::* ;
    let factory = Factory::mk() ;

    let bla_plus_7 = factory.op(
      Operator::Add, vec![
        factory.var( factory.sym("bla") ),
        factory.cst( Int::from_str("7").unwrap() )
      ]
    ) ;
    let mut s: Vec<u8> = vec![] ;
    bla_plus_7.to_sts2(& mut s).unwrap() ;
    try_parse_term!(
      term_parser, & factory,
      & s,
      bla_plus_7
    ) ;

    let nested = factory.op(
      Operator::Le, vec![
        factory.cst( Int::from_str("17").unwrap() ),
        bla_plus_7
      ]
    ) ;
    let mut s: Vec<u8> = vec![] ;
    nested.to_sts2(& mut s).unwrap() ;
    try_parse_term!(
      term_parser, & factory,
      & s,
      nested
    ) ;

    let nested = factory.op(
      Operator::And, vec![
        factory.svar( factory.sym("svar"), State::Curr ),
        nested
      ]
    ) ;
    let mut s: Vec<u8> = vec![] ;
    nested.to_sts2(& mut s).unwrap() ;
    try_parse_term!(
      term_parser, & factory,
      & s,
      nested
    ) ;

    let nested = factory.op(
      Operator::Or, vec![
        factory.svar( factory.sym("something else"), State::Next ),
        nested
      ]
    ) ;
    let mut s: Vec<u8> = vec![] ;
    nested.to_sts2(& mut s).unwrap() ;
    try_parse_term!(
      term_parser, & factory,
      & s,
      nested
    ) ;

    let nested = factory.op(
      Operator::Ite, vec![
        factory.var( factory.sym("bla.bla") ),
        factory.op(
          Operator::Eq, vec![
            factory.var( factory.sym("bli.blu") ),
            factory.cst( Int::from_str("1").unwrap() )
          ]
        ),
        factory.op(
          Operator::Eq, vec![
            factory.var( factory.sym("bli.blu") ),
            factory.cst( Int::from_str("0").unwrap() )
          ]
        ),
      ]
    ) ;
    let mut s: Vec<u8> = vec![] ;
    nested.to_sts2(& mut s).unwrap() ;
    try_parse_term!(
      term_parser, & factory,
      & s,
      nested
    ) ;
  }

  #[test]
  fn app() {
    use super::* ;
    let factory = Factory::mk() ;

    let bla_plus_7 = factory.app(
      factory.sym("function symbol"), vec![
        factory.var( factory.sym("bla") ),
        factory.cst( Int::from_str("7").unwrap() )
      ]
    ) ;
    let mut s: Vec<u8> = vec![] ;
    bla_plus_7.to_sts2(& mut s).unwrap() ;
    try_parse_term!(
      term_parser, & factory,
      & s,
      bla_plus_7
    ) ;

    let nested = factory.app(
      factory.sym("another function symbol"), vec![
        factory.cst( Int::from_str("17").unwrap() ),
        bla_plus_7
      ]
    ) ;
    let mut s: Vec<u8> = vec![] ;
    nested.to_sts2(& mut s).unwrap() ;
    try_parse_term!(
      term_parser, & factory,
      & s,
      nested
    ) ;

    let nested = factory.app(
      factory.sym("yet another one"), vec![
        factory.svar( factory.sym("svar"), State::Curr ),
        nested
      ]
    ) ;
    let mut s: Vec<u8> = vec![] ;
    nested.to_sts2(& mut s).unwrap() ;
    try_parse_term!(
      term_parser, & factory,
      & s,
      nested
    ) ;

    let nested = factory.op(
      Operator::Or, vec![
        factory.svar( factory.sym("something else"), State::Next ),
        nested
      ]
    ) ;
    let mut s: Vec<u8> = vec![] ;
    nested.to_sts2(& mut s).unwrap() ;
    try_parse_term!(
      term_parser, & factory,
      & s,
      nested
    ) ;
  }

  #[test]
  fn empty() {
    use super::* ;
    let factory = Factory::mk() ;
    match super::term_parser(& b""[..], & factory) {
      ::nom::IResult::Incomplete(_) => (),
      other => panic!("unexpected result on parsing empty string: {:?}", other)
    } ;
    ()
  }
}

