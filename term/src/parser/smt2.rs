// Copyright 2015 Adrien Champion. See the COPYRIGHT file at the top-level
// directory of this distribution.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

/*! Parsers for answers to SMT Lib 2.5 queries. */

use std::str ;
use std::fmt::Debug ;

use nom::{ multispace, IResult } ;

use base::{ State, Offset, Offset2, Smt2Offset } ;
use typ::Type ;
use sym::Sym ;
use term::{ Term, Operator } ;
use factory::{ Factory, UnTermOps } ;

use super::{
  type_parser,
  simple_symbol_head, simple_symbol_tail,
  operator_parser,
  quantifier_parser, Quantifier
} ;

trait TermApply: Sized {
  fn apply<
    F: Fn(Term) -> Result<Term,()>
  >(& self, F) -> Result<Self, ()> ;
}
impl TermApply for Term {
  fn apply<
    F: Fn(Term) -> Result<Term,()>
  >(& self, f: F) -> Result<Self, ()> { f(self.clone()) }
}
impl TermApply for (Sym, Term) {
  fn apply<
    F: Fn(Term) -> Result<Term,()>
  >(& self, f: F) -> Result<Self, ()> {
    match f(self.1.clone()) {
      Ok(t) => Ok( (self.0.clone(), t) ),
      Err(()) => Err(()),
    }
  }
}

trait Mergeable<Out: TermApply> {
  fn merge(self, Term) -> Out ;
}
impl Mergeable<Term> for () {
  fn merge(self, t: Term) -> Term { t }
}
impl Mergeable<(Sym, Term)> for Sym {
  fn merge(self, t: Term) -> (Sym, Term) { (self, t) }
}

trait HasTermInfo<Out: TermApply, T: Mergeable<Out>> {
  fn term_info(self) -> ( (Term, Smt2Offset), T ) ;
}
impl HasTermInfo<Term, ()> for (Term, Smt2Offset) {
  fn term_info(self) -> ( (Term, Smt2Offset), () ) { (self, ()) }
}
impl HasTermInfo<(Sym, Term), Sym> for (Sym, (Term, Smt2Offset)) {
  fn term_info(self) -> ( (Term, Smt2Offset), Sym ) { (self.1, self.0) }
}


fn check_offsets<
  Out: TermApply + Debug, Temp: Mergeable<Out>, T: HasTermInfo<Out, Temp>
>(
  f: & Factory, mut terms: Vec<T>, cmp: & Offset2
) -> (Vec<Out>, Smt2Offset) {
  use base::Smt2Offset::* ;
  use std::iter::FromIterator ;
  let mut res = Vec::with_capacity( terms.len() ) ;
  let mut off = No ;
  loop {
    if let Some( t ) = terms.pop() {
      let ( (term, info), something ) = t.term_info() ;
      match off.merge(& info, cmp) {
        Some(nu_info) => {
          if info.is_next_of(& nu_info) {
            off = nu_info ;
            // Offset of term is new next, bump term.
            res.push(
              match f.bump(term.clone()) {
                Ok(t) => something.merge(t),
                Err(()) => panic!("cannot bump {:?}", term),
              }
            )
          } else {
            // Previous offset is now next, bump all terms.
            if off.is_next_of(& nu_info) {
              res = Vec::from_iter(
                res.into_iter().map(
                  |t| match t.apply(|t| f.bump(t)) {
                    Ok(t) => t,
                    Err(()) => panic!(
                      "cannot bump {:?}", t
                    ),
                  }
                )
              )
            } ;
            off = nu_info ;
            res.push( something.merge(term) )
          }
        }
        None => {
          panic!("cannot merge {:?} and {:?}", off, info)
        },
      }
    } else { break }
  }
  res.reverse() ;
  (res, off)
}

fn mk_op(
  f: & Factory, op: Operator, args: (Vec<Term>, Smt2Offset)
) -> (Term,Smt2Offset) {
  use term::OpMaker ;
  let (args, off) = args ;
  ( f.op(op, args), off )
}

fn mk_app(
  f: & Factory,
  (sym, sym_off): (String, Smt2Offset),
  (args, off): (Vec<Term>, Smt2Offset)
) -> (Term, Smt2Offset) {
  use sym::SymMaker ;
  use term::AppMaker ;
  match sym_off {
    Smt2Offset::No => {
      let sym = f.sym(sym) ;
      ( f.app(sym, args), off )
    },
    _ => panic!(
      "application of symbol {} with offset {:?}", sym, sym_off
    ),
  }
}

fn mk_forall(
  f: & Factory,
  bindings: Vec<(Sym, Type)>,
  (term, off): (Term, Smt2Offset)
) -> (Term, Smt2Offset) {
  use term::BindMaker ;
  ( f.forall(bindings, term), off )
}

fn mk_exists(
  f: & Factory,
  bindings: Vec<(Sym, Type)>,
  (term, off): (Term, Smt2Offset)
) -> (Term, Smt2Offset) {
  use term::BindMaker ;
  ( f.exists(bindings, term), off )
}

fn mk_let(
  f: & Factory,
  bindings: Vec<(Sym, (Term, Smt2Offset))>,
  (term, off): (Term, Smt2Offset),
  cmp: & Offset2,
) -> (Term, Smt2Offset) {
  use term::BindMaker ;
  use std::iter::FromIterator ;
  let (bindings, off_b) = check_offsets(f, bindings, cmp) ;
  match off.merge(& off_b, cmp) {
    Some(nu_off) => {
      let (bindings, term) = {
        if off.is_next_of(& nu_off) {
          // Term is in next step, need to bump.
          match f.bump(term.clone()) {
            Ok(t) => (bindings, t),
            Err(()) => panic!("can't bump {:?}", term),
          }
        } else {
          if off_b.is_next_of(& nu_off) {
            // Bindings are in next step, need to bump.
            let bindings = Vec::from_iter(
              bindings.into_iter().map(
                |t| match t.apply(|t| f.bump(t)) {
                  Ok(t) => t,
                  Err(()) => panic!(
                    "cannot bump {:?}", t
                  ),
                }
              )
            ) ;
            (bindings, term)
          } else { (bindings, term) }
        }
      } ;
      ( f.let_b(bindings, term), off )
    },
    None => panic!(
      "cannot merge {:?} with {:?}", off_b, off
    ),
  }
}

named!{ offset<Offset>,
  chain!(
    char!('@') ~
    offset: is_a!("0123456789"),
    || Offset::of_bytes(offset)
  )
}

named!{ pub id_parser< (String, Smt2Offset) >,
  preceded!(
    opt!(multispace),
    alt!(
      // Simple symbol.
      chain!(
        opt!(offset) ~
        head: simple_symbol_head ~
        tail: opt!(
          map!( simple_symbol_tail, |bytes| str::from_utf8(bytes).unwrap() )
        ),
        || {
          let sym = format!("{}{}", head, tail.unwrap_or("")) ;
          panic!("simple symbol {}", sym)
        }
        // (
        //   format!("{}{}", head, str::from_utf8(tail).unwrap()),
        //   Smt2Offset::of_opt(offset)
        // )
      ) |
      // Quoted symbol.
      delimited!(
        char!('|'),
        chain!(
          offset: opt!(offset) ~
          char!(' ') ~
          sym: map!(
            is_not!("|\\"), str::from_utf8
          ),
          || (
            sym.unwrap().to_string(), Smt2Offset::of_opt(offset)
          )
        ),
        char!('|')
      )
    )
  )
}

fn cst_parser<'a>(
  bytes: & 'a [u8], f: & Factory
) -> IResult<'a, & 'a [u8], ( Term, Smt2Offset )> {
  use term::CstMaker ;
  map!(
    bytes,
    apply!( super::cst_parser, f.cst_consign() ),
    |cst| ( f.cst(cst), Smt2Offset::No )
  )
}


fn var_parser<'a>(
  bytes: & 'a [u8], f: & Factory
) -> IResult<'a, & 'a [u8], ( Term, Smt2Offset )> {
  use var::VarMaker ;
  map!(
    bytes,
    id_parser,
    |(id,info): (String, Smt2Offset)| match info {
      Smt2Offset::No => ( f.var(id), info ),
      Smt2Offset::One(_) => ( f.svar(id, State::Curr), info ),
      _ => unreachable!(),
    }
  )
}

fn op_parser<'a>(
  bytes: & 'a [u8], f: & Factory, off: & Offset2
) -> IResult<'a, & 'a [u8], ( Term, Smt2Offset )> {
  chain!(
    bytes,
    char!('(') ~
    opt!(multispace) ~
    op: operator_parser ~
    multispace ~
    args: map!(
      separated_list!(
        multispace, apply!(term_parser, f, off)
      ),
      |args| check_offsets(f, args, off)
    ) ~
    opt!(multispace) ~
    char!(')'),
    || mk_op(& f, op, args)
  )
}



fn quantified_parser<'a>(
  bytes: & 'a [u8], f: & Factory, off: & Offset2
) -> IResult<'a, & 'a [u8], ( Term, Smt2Offset )> {
  use sym::SymMaker ;
  chain!(
    bytes,
    char!('(') ~
    opt!(multispace) ~
    quantifier: quantifier_parser ~
    opt!(multispace) ~
    char!('(') ~
    bindings: separated_list!(
      opt!(multispace),
      delimited!(
        char!('('),
        chain!(
          opt!(multispace) ~
          sym: map!(
            id_parser,
            |(s,off)| match off {
              Smt2Offset::No => f.sym(s),
              _ => panic!("offset in bound variable"),
            }
          ) ~
          multispace ~
          ty: type_parser ~
          opt!(multispace),
          || (sym, ty)
        ),
        char!(')')
      )
    ) ~
    opt!(multispace) ~
    char!(')') ~
    opt!(multispace) ~
    term: apply!(term_parser, f, off) ~
    opt!(multispace) ~
    char!(')'),
    || match quantifier {
      Quantifier::Forall => mk_forall(f, bindings, term),
      Quantifier::Exists => mk_exists(f, bindings, term),
    }
  )
}



fn let_parser<'a>(
  bytes: & 'a [u8], f: & Factory, off: & Offset2
) -> IResult<'a, & 'a [u8], ( Term, Smt2Offset )> {
  use sym::SymMaker ;
  chain!(
    bytes,
    char!('(') ~
    opt!(multispace) ~
    tag!("let") ~
    opt!(multispace) ~
    char!('(') ~
    bindings: separated_list!(
      opt!(multispace),
      delimited!(
        char!('('),
        chain!(
          opt!(multispace) ~
          sym: map!(
            id_parser,
            |(s,off)| match off {
              Smt2Offset::No => f.sym(s),
              _ => panic!(
                "offset in bound variable"
              ),
            }
          ) ~
          multispace ~
          term: apply!(term_parser, f, off) ~
          opt!(multispace),
          || (sym, term)
        ),
        char!(')')
      )
    ) ~
    opt!(multispace) ~
    char!(')') ~
    opt!(multispace) ~
    term: apply!(term_parser, f, off) ~
    opt!(multispace) ~
    char!(')'),
    || mk_let(f, bindings, term, off)
  )
}


fn app_parser<'a>(
  bytes: & 'a [u8], f: & Factory, off: & Offset2
) -> IResult<'a, & 'a [u8], ( Term, Smt2Offset )> {
  chain!(
    bytes,
    char!('(') ~
    opt!(multispace) ~
    id: id_parser ~
    multispace ~
    args: map!(
      separated_list!(
        multispace, apply!(term_parser, f, off)
      ),
      |args| check_offsets(f, args, off)
    ) ~
    opt!(multispace) ~
    char!(')'),
    || mk_app(f, id, args)
  )
}

pub fn term_parser<'a>(
  bytes: & 'a [u8], f: & Factory, off: & Offset2
) -> IResult<'a, & 'a [u8], ( Term, Smt2Offset )> {
  alt!(
    bytes,
    apply!(cst_parser, f) |
    apply!(var_parser, f) |
    apply!(op_parser, f, off) |
    apply!(quantified_parser, f, off) |
    apply!(let_parser, f, off) |
    apply!(app_parser, f, off)
  )
}





#[cfg(test)]
macro_rules! try_parse_id {
  ($fun:expr, $arg:expr, $state:expr, $id:expr) => (
    try_parse!($fun, $arg,
      (s, res) -> {
        let (id, state) = res ;
        let exp = $state ;
        if exp != state {
          panic!("expected state {:?}, got {:?}", exp, state)
        } else {
          assert_eq!(id, $id)
        }
      }
    )
  ) ;
  ($fun:expr, $arg:expr, $state:expr) => (
    try_parse_id!(
      $fun, $arg, $state, ::std::str::from_utf8($arg).unwrap()
    )
  ) ;
}


#[cfg(test)]
macro_rules! try_parse_term {
  ($fun:expr, $factory:expr, $arg:expr, $off:expr, $e:expr) => (
    try_parse!($fun, $factory, $arg,
      (s, res) -> {
        let (term, off) = res ;
        if off != $off {
          panic!("expected {:?}, got {:?}", $off, off)
        } else {
          assert_eq!(term, $e)
        }
      }
    )
  ) ;
}

// #[cfg(test)]
// mod simpl_sym {
//   use base::Offset ;
//   use base::Smt2Offset::* ;
//   #[test]
//   fn nsvar() {
//     use super::* ;
//     try_parse_id!(id_parser, b"bla", No, "bla") ;
//     try_parse_id!(id_parser, b"_bla!52740>^^&", No, "_bla!52740>^^&") ;
//   }
//   #[test]
//   fn svar() {
//     use super::* ;
//     try_parse_id!(id_parser, b"@7bla", One(Offset::of_int(7)), "bla") ;
//     try_parse_id!(
//       id_parser, b"@42!52@_740>^^&",
//       One(Offset::of_int(42)), "!52@_740>^^&"
//     ) ;
//   }
// }

#[cfg(test)]
mod quoted_sym {
  use base::Offset ;
  use base::Smt2Offset::* ;
  #[test]
  fn nsvar() {
    use super::* ;
    try_parse_id!(id_parser, b"| bla|", No, "bla") ;
    try_parse_id!(
      id_parser, b"| [{}_b}(l=a}(!**52)740>^^&|",
      No, "[{}_b}(l=a}(!**52)740>^^&"
    ) ;
  }
  #[test]
  fn svar() {
    use super::* ;
    try_parse_id!(id_parser, b"|@7 bla|", One(Offset::of_int(7)), "bla") ;
    try_parse_id!(
      id_parser, b"|@42 [{!+)*(![{}+=*!/~%75!52@_740>^^&|",
      One(Offset::of_int(42)), "[{!+)*(![{}+=*!/~%75!52@_740>^^&"
    ) ;
  }
}

#[cfg(test)]
mod terms {
  use base::{ State, Offset, Smt2Offset, Offset2, PrintSmt2 } ;
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
      Smt2Offset::No,
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
      Smt2Offset::No,
      res
    ) ;
    let res = factory.cst( true ) ;
    try_parse_term!(
      term_parser, & factory,
      b"true",
      Smt2Offset::No,
      res
    ) ;
    let res = factory.cst( false ) ;
    try_parse_term!(
      term_parser, & factory,
      b"false",
      Smt2Offset::No,
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
      b"| bla|",
      Smt2Offset::No,
      res
    ) ;
    let res = factory.svar( factory.sym("bla"), State::Curr ) ;
    try_parse_term!(
      term_parser, & factory,
      b"|@7 bla|",
      Smt2Offset::One(Offset::of_int(7)),
      res
    ) ;
    try_parse_term!(
      term_parser, & factory,
      b"|@8 bla|",
      Smt2Offset::One(Offset::of_int(8)),
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
    let offset = & Offset2::init() ;
    let mut s: Vec<u8> = vec![] ;
    bla_plus_7.to_smt2(& mut s, offset).unwrap() ;
    try_parse_term!(
      term_parser, & factory,
      & s,
      Smt2Offset::No,
      bla_plus_7
    ) ;

    let nested = factory.op(
      Operator::Le, vec![
        factory.cst( Int::from_str("17").unwrap() ),
        bla_plus_7
      ]
    ) ;
    let mut s: Vec<u8> = vec![] ;
    nested.to_smt2(& mut s, offset).unwrap() ;
    try_parse_term!(
      term_parser, & factory,
      & s,
      Smt2Offset::No,
      nested
    ) ;

    let nested = factory.op(
      Operator::And, vec![
        factory.svar( factory.sym("svar"), State::Curr ),
        nested
      ]
    ) ;
    let offset = & offset.nxt().nxt() ;
    let mut s: Vec<u8> = vec![] ;
    nested.to_smt2(& mut s, offset).unwrap() ;
    try_parse_term!(
      term_parser, & factory,
      & s,
      Smt2Offset::One( Offset::of_int(2) ),
      nested
    ) ;

    let nested = factory.op(
      Operator::Or, vec![
        factory.svar( factory.sym("something else"), State::Next ),
        nested
      ]
    ) ;
    let offset = & offset.nxt().nxt() ;
    let mut s: Vec<u8> = vec![] ;
    nested.to_smt2(& mut s, offset).unwrap() ;
    try_parse_term!(
      term_parser, & factory,
      & s,
      Smt2Offset::Two( Offset::of_int(4), Offset::of_int(5) ),
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
    let offset = & Offset2::init() ;
    let mut s: Vec<u8> = vec![] ;
    bla_plus_7.to_smt2(& mut s, offset).unwrap() ;
    try_parse_term!(
      term_parser, & factory,
      & s,
      Smt2Offset::No,
      bla_plus_7
    ) ;

    let nested = factory.app(
      factory.sym("another function symbol"), vec![
        factory.cst( Int::from_str("17").unwrap() ),
        bla_plus_7
      ]
    ) ;
    let mut s: Vec<u8> = vec![] ;
    nested.to_smt2(& mut s, offset).unwrap() ;
    try_parse_term!(
      term_parser, & factory,
      & s,
      Smt2Offset::No,
      nested
    ) ;

    let nested = factory.app(
      factory.sym("yet another one"), vec![
        factory.svar( factory.sym("svar"), State::Curr ),
        nested
      ]
    ) ;
    let offset = & offset.nxt().nxt() ;
    let mut s: Vec<u8> = vec![] ;
    nested.to_smt2(& mut s, offset).unwrap() ;
    try_parse_term!(
      term_parser, & factory,
      & s,
      Smt2Offset::One( Offset::of_int(2) ),
      nested
    ) ;

    let nested = factory.op(
      Operator::Or, vec![
        factory.svar( factory.sym("something else"), State::Next ),
        nested
      ]
    ) ;
    let offset = & offset.nxt().nxt() ;
    let mut s: Vec<u8> = vec![] ;
    nested.to_smt2(& mut s, offset).unwrap() ;
    try_parse_term!(
      term_parser, & factory,
      & s,
      Smt2Offset::Two( Offset::of_int(4), Offset::of_int(5) ),
      nested
    ) ;
  }
}