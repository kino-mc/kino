// Copyright 2015 Adrien Champion. See the COPYRIGHT file at the top-level
// directory of this distribution.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

/*! Parsers and such. */

use nom::{ multispace, IResult } ;

use cst::ConstMaker ;

use typ::{ Type, Bool, Int, Rat } ;
use cst::Cst ;
use term::Operator ;

/** Used in tests for parsers. */
#[cfg(test)]
macro_rules! try_parse {
  (
    $fun:expr, $factory:expr, $arg:expr,
    ($s:ident, $res:ident) -> $b:block
  ) => (
    {
      let $s = ::std::str::from_utf8($arg).unwrap() ;
      println!("| parsing \"{}\"", $s) ;
      match $fun(& $arg[..], $factory) {
        ::nom::IResult::Done(_,$res) => {
          println!("| done: {:?}", $res) ;
          $b
        },
        ::nom::IResult::Error(
          ::nom::Err::Position(pos,txt)
        ) => panic!(
          "position error at {}: {}",
          pos, ::std::str::from_utf8(txt).unwrap()
        ),
        ::nom::IResult::Error(e) => panic!("error: {:?}", e),
        ::nom::IResult::Incomplete(n) => panic!("incomplete: {:?}", n),
      } ;
      println!("") ;
    }
  ) ;
  ($fun:expr, $arg:expr, ($s:ident, $res:ident) -> $b:block) => (
    {
      let $s = ::std::str::from_utf8($arg).unwrap() ;
      println!("| parsing \"{}\"", $s) ;
      match $fun(& $arg[..]) {
        ::nom::IResult::Done(_,$res) => {
          println!("| done: {:?}", $res) ;
          $b
        },
        ::nom::IResult::Error(e) => panic!("error: {:?}", e),
        ::nom::IResult::Incomplete(n) => panic!("incomplete: {:?}", n),
      } ;
      println!("") ;
    }
  ) ;
  ($fun:expr, $arg:expr) => (
    try_parse!($fun, $arg, (s,r) -> { () })
  ) ;
}

pub mod smtrans ;
pub mod smt2 ;

named!{ pub type_parser<Type>,
  alt!(
    map!( tag!("Int"),  |_| Type::Int  ) |
    map!( tag!("Bool"), |_| Type::Bool ) |
    map!( tag!("Real"),  |_| Type::Rat  )
  )
}



named!{ pub bool_parser<Bool>,
  alt!(
    chain!(
      char!('t') ~
      char!('r') ~
      char!('u') ~
      char!('e'),
      || true
    ) |
    chain!(
      char!('f') ~
      char!('a') ~
      char!('l') ~
      char!('s') ~
      char!('e'),
      || false
    )
  )
}

named!{ pub int_parser<Int>,
  map!(
    is_a!("0123456789"),
    // Unwraping cannot fail.
    |bytes| Int::parse_bytes(bytes, 10).unwrap()
  )
}

named!{ pub rat_parser<Rat>,
  alt!(
    chain!(
      char!('(') ~
      opt!(multispace) ~
      char!('/') ~
      multispace ~
      num: int_parser ~
      multispace ~
      den: int_parser ~
      opt!(multispace) ~
      char!(')'),
      // Unchecked division by 0.
      || Rat::new(num, den)
    )
  )
}

pub fn cst_parser<
  'a, F: ConstMaker<Bool> + ConstMaker<Int> + ConstMaker<Rat>
>(
  bytes: & 'a [u8], f: & F
) -> IResult<'a, & 'a [u8], Cst> {
  alt!(
    bytes,
    map!( int_parser, |i| f.constant(i) ) |
    map!( rat_parser, |r| f.constant(r) ) |
    map!( bool_parser, |b| f.constant(b) )
  )
}

/** Matches the head of a simple symbol. */
named!{ pub simple_symbol_head<char>,
  one_of!("\
    _\
    abcdefghijklmnopqrstuvwxyz\
    ABCDEFGHIJKLMNOPQRSTUVWXYZ\
    ~!$%^&*_-+=<>.?/
  ")
}

/** Matches the tail of a simple symbol. */
named!{ pub simple_symbol_tail,
  is_a!("\
    _\
    0123456789\
    abcdefghijklmnopqrstuvwxyz\
    ABCDEFGHIJKLMNOPQRSTUVWXYZ\
    ~!@$%^&*_-+=<>.?/
  ")
}



named!{ pub operator_parser<Operator>,
  alt!(
    map!( tag!("ite"), |_| Operator::Ite ) |
    map!( tag!("not"), |_| Operator::Not ) |
    map!( tag!("and"), |_| Operator::And ) |
    map!( tag!("or"), |_| Operator::Or ) |
    map!( tag!("impl"), |_| Operator::Impl ) |
    map!( tag!("xor"), |_| Operator::Xor ) |
    map!( tag!("distinct"), |_| Operator::Distinct ) |
    map!( tag!("+"), |_| Operator::Add ) |
    map!( tag!("-"), |_| Operator::Sub ) |
    map!( tag!("-"), |_| Operator::Neg ) |
    map!( tag!("*"), |_| Operator::Mul ) |
    map!( tag!("/"), |_| Operator::Div ) |
    map!( tag!("<="), |_| Operator::Le ) |
    map!( tag!(">="), |_| Operator::Ge ) |
    map!( tag!("<"), |_| Operator::Lt ) |
    map!( tag!(">"), |_| Operator::Gt )
  )
}


enum Quantifier {
  Forall, Exists
}

named!{ quantifier_parser<Quantifier>,
  alt!(
    map!( tag!("forall"), |_| Quantifier::Forall ) |
    map!( tag!("exists"), |_| Quantifier::Exists )
  )
}



// pub enum TermAst {
//   App(Sym),
//   Forall(Vec<(Sym, Type)>),
//   Exists(Vec<(Sym, Type)>),
//   Let1,
//   Let2(Sym, Vec<(Sym, Term)>),
//   Let3(Vec<(Sym, Term)>),
// }

// impl TermAst {
//   pub fn name(& self) -> & 'static str {
//     match * self {
//       App(_) => "application"

//     }
//   }
// }

// pub struct Ast<'a> {
//   cons: & 'a TermConsign,
//   top: Vec<Term>,
//   ctxt: Vec<(TermAst,Vec<Term>)>,
// }


// impl<'a> Ast<'a> {
//   pub fn mk(consign: & 'a TermConsign) -> Self {
//     Ast { cons: consign, top: vec![], ctxt: vec![] }
//   }

//   pub fn app(& mut self, sym: Sym) {
//     self.ctxt.push( TermAst::App(sym) )
//   }
//   pub fn forall(& mut self, vars: Vec<(Sym, Type)>) {
//     self.ctxt.push( TermAst::Forall(vars) )
//   }
//   pub fn exists(& mut self, vars: Vec<(Sym, Type)>) {
//     self.ctxt.push( TermAst::Exists(vars) )
//   }
//   pub fn let_b(& mut self) {
//     self.ctxt.push( TermAst::Let1( vec![] ) )
//   }
//   pub fn binding_sym(& mut self, sym: Sym) -> Result<(), TermAst> {
//     match self.ctxt.pop() {
//       (Let1, terms) => {
//         assert!( terms.is_empty() ) ;
//         self.ctxt.push( Let2(Sym, vec![]) ) ;
//         Ok(())
//       },
//       (Let3(bindings), terms) => {
//         assert!( terms.is_empty() ) ;
//         self.ctxt.push( Let2(Sym, vec![]) ) ;
//         Ok(())
//       },
//       (illegal, terms) => Err(illegal),
//     }
//   }

//   pub fn leaf(& mut self, mut term: Term) {
//     match self.ctxt.pop() {
//       Some( (something, terms) ) => {
//         terms.push(term) ;
//         self.ctxt.push( (something, terms) )
//       }
//       None => self.top.push(term),
//     }
//   }

//   // pub fn go_up(& mut self) {
//   //   match self.ctxt.
//   // }
// }








#[cfg(test)]
macro_rules! try_parse_val {
  ($fun:expr, $arg:expr, $val:expr) => (
    try_parse!($fun, $arg,
      (s, val) -> { assert_eq!(val, $val) }
    )
  ) ;
}

#[cfg(test)]
mod typ3 {
  #[test]
  fn boo1() {
    use super::* ;
    try_parse_val!(
      type_parser, b"Bool", ::typ::Type::Bool
    )
  }
  #[test]
  fn int() {
    use super::* ;
    try_parse_val!(
      type_parser, b"Int", ::typ::Type::Int
    )
  }
  #[test]
  fn rat() {
    use super::* ;
    try_parse_val!(
      type_parser, b"Real", ::typ::Type::Rat
    )
  }
}


#[cfg(test)]
mod boo1 {
  #[test]
  fn tru3() {
    use super::* ;
    try_parse_val!(
      bool_parser, b"true", true
    )
  }
  #[test]
  fn fals3() {
    use super::* ;
    try_parse_val!(
      bool_parser, b"false", false
    )
  }
}

#[cfg(test)]
mod int {
  #[test]
  fn int() {
    use super::* ;
    use std::str::FromStr ;
    use typ::Int ;
    try_parse_val!(
      int_parser, b"42", Int::from_str("42").unwrap()
    ) ;
    try_parse_val!(
      int_parser, b"74205432075342042",
      Int::from_str("74205432075342042").unwrap()
    )
  }
}

#[cfg(test)]
mod rat {
  #[test]
  fn rat() {
    use super::* ;
    use std::str::FromStr ;
    use typ::{ Int, Rat } ;
    try_parse_val!(
      rat_parser, b"(/ 0 1)",
      Rat::new(
        Int::from_str("0").unwrap(),
        Int::from_str("1").unwrap()
      )
    ) ;
    try_parse_val!(
      rat_parser, b"( / 74205432075342042 76453   )",
      Rat::new(
        Int::from_str("74205432075342042").unwrap(),
        Int::from_str("76453").unwrap()
      )
    )
  }
}