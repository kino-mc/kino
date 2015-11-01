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

use nom::{ multispace, IResult } ;

use base::State ;
use term::{ Term, VarMaker } ;
use factory::Factory ;

use super::{
  type_parser,
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
      opt!(multispace) ~
      state: state ~
      multispace ~
      sym: map!(
        id_parser, |s| f.sym(s)
      ) ~
      opt!(multispace) ~
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
    opt!(multispace) ~
    op: operator_parser ~
    multispace ~
    args: separated_list!(
      multispace, apply!(term_parser, f)
    ) ~
    opt!(multispace) ~
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
            |sym| f.sym(sym)
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
    term: apply!(term_parser, f) ~
    opt!(multispace) ~
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
            |sym| f.sym(sym)
          ) ~
          multispace ~
          term: apply!(term_parser, f) ~
          opt!(multispace),
          || (sym, term)
        ),
        char!(')')
      )
    ) ~
    opt!(multispace) ~
    char!(')') ~
    opt!(multispace) ~
    term: apply!(term_parser, f) ~
    opt!(multispace) ~
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
    opt!(multispace) ~
    sym: id_parser ~
    multispace ~
    args: separated_list!(
      multispace, apply!(term_parser, f)
    ) ~
    opt!(multispace) ~
    char!(')'),
    || f.app( f.sym(sym), args )
  )
}


pub fn term_parser<'a>(
  bytes: & 'a [u8], f: & Factory
) -> IResult<'a, & 'a [u8], Term> {
  alt!(
    bytes,
    apply!(var_parser, f) |
    apply!(cst_parser, f) |
    apply!(op_parser, f) |
    apply!(quantified_parser, f) |
    apply!(let_parser, f) |
    apply!(app_parser, f)
  )
}







// #[cfg(test)]
// macro_rules! try_parse_id {
//   ($fun:expr, $arg:expr, $state:expr, $id:expr) => (
//     try_parse!($fun, $arg,
//       (s, res) -> {
//         let (id, state) = res ;
//         let exp: Option<State> = $state ;
//         if exp != state {
//           panic!("expected state {:?}, got {:?}", exp, state)
//         } else {
//           assert_eq!(id, $id)
//         }
//       }
//     )
//   ) ;
//   ($fun:expr, $arg:expr, $state:expr) => (
//     try_parse_id!(
//       $fun, $arg, $state, ::std::str::from_utf8($arg).unwrap()
//     )
//   ) ;
// }

// #[cfg(test)]
// mod simpl_sym {
//   use term::State ;
//   #[test]
//   fn nsvar() {
//     use super::* ;
//     try_parse_id!(id_parser, b"bla", None, "bla") ;
//     try_parse_id!(id_parser, b"_bla!52740>^^&", None, "_bla!52740>^^&") ;
//   }
//   #[test]
//   fn svar0() {
//     use super::* ;
//     try_parse_id!(id_parser, b"state.bla", Some(State::Curr), "bla") ;
//     try_parse_id!(
//       id_parser, b"state.!52@_740>^^&", Some(State::Curr), "!52@_740>^^&"
//     ) ;
//   }
//   #[test]
//   fn svar1() {
//     use super::* ;
//     try_parse_id!(id_parser, b"next.bla", Some(State::Next), "bla") ;
//     try_parse_id!(
//       id_parser, b"next._sath%mis?/$$0", Some(State::Next), "_sath%mis?/$$0"
//     ) ;
//   }
//   #[test]
//   #[should_panic]
//   fn illegal_first_is_digit() {
//     use super::* ;
//     try_parse!(id_parser, b"7bla") ;
//   }
//   #[test]
//   #[should_panic]
//   fn illegal_first_is_at() {
//     use super::* ;
//     try_parse!(id_parser, b"@bla") ;
//     try_parse!(id_parser, b"state.@bla") ;
//     try_parse!(id_parser, b"next.@bla") ;
//   }
// }

// #[cfg(test)]
// mod quoted_sym {
//   use term::State ;
//   #[test]
//   fn nsvar() {
//     use super::* ;
//     try_parse_id!(id_parser, b"|bla|", None, "bla") ;
//     try_parse_id!(
//       id_parser, b"|b  ;][&])=(!&]+)=$&[]})*=la!52740>^^&|",
//       None, "b  ;][&])=(!&]+)=$&[]})*=la!52740>^^&"
//     ) ;
//   }
//   #[test]
//   fn svar0() {
//     use super::* ;
//     try_parse_id!(id_parser, b"|state.bla|", Some(State::Curr), "bla") ;
//     try_parse_id!(
//       id_parser, b"|state.[ !52@_74;[&{(0>^^]*!#&// |",
//       Some(State::Curr), "[ !52@_74;[&{(0>^^]*!#&// "
//     ) ;
//   }
//   #[test]
//   fn svar1() {
//     use super::* ;
//     try_parse_id!(id_parser, b"|next.bla|", Some(State::Next), "bla") ;
//     try_parse_id!(
//       id_parser, b"|next._sa%~3^^^\"th%mis?{}]+)!#/$$0|",
//     Some(State::Next), "_sa%~3^^^\"th%mis?{}]+)!#/$$0"
//     ) ;
//   }
//   #[test]
//   #[should_panic]
//   fn illegal_first_is_at() {
//     use super::* ;
//     try_parse!(id_parser, b"|@bla|") ;
//     try_parse!(id_parser, b"|state.@bla|") ;
//     try_parse!(id_parser, b"|next.@bla|") ;
//   }
// }