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

use nom::{ IResult } ;

use base::State ;
use var::VarMaker ;
use term::Term ;
use factory::Factory ;

use super::{
  type_parser,
  space_comment,
  simple_symbol_head, simple_symbol_tail,
  operator_parser,
  quantifier_parser, Quantifier
} ;

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
) -> IResult<'a, & 'a [u8], Term> {
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
      || f.svar(sym, state)
    ) |
    map!(
      id_parser, |s| f.var( f.sym(s) )
    )
  )
}

pub fn cst_parser<'a>(
  bytes: & 'a [u8], f: & Factory
) -> IResult<'a, & 'a [u8], Term> {
  use term::CstMaker ;
  map!(
    bytes,
    apply!( super::cst_parser, f.cst_consign() ),
    |cst| f.cst(cst)
  )
}

pub fn op_parser<'a>(
  bytes: & 'a [u8], f: & Factory
) -> IResult<'a, & 'a [u8], Term> {
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
    || f.op(op, args)
  )
}


pub fn quantified_parser<'a>(
  bytes: & 'a [u8], f: & Factory
) -> IResult<'a, & 'a [u8], Term> {
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
      Quantifier::Forall => f.forall(bindings, term),
      Quantifier::Exists => f.exists(bindings, term),
    }
  )
}

pub fn let_parser<'a>(
  bytes: & 'a [u8], f: & Factory
) -> IResult<'a, & 'a [u8], Term> {
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
    || f.let_b(bindings, term)
  )
}

fn app_parser<'a>(
  bytes: & 'a [u8], f: & Factory
) -> IResult<'a, & 'a [u8], Term> {
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
    || f.app( f.sym(sym), args )
  )
}


pub fn term_parser<'a>(
  bytes: & 'a [u8], f: & Factory
) -> IResult<'a, & 'a [u8], Term> {
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

