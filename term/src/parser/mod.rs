// Copyright 2015 Adrien Champion. See the COPYRIGHT file at the top-level
// directory of this distribution.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! Parsers and such.

use std::ops::{ Deref, DerefMut } ;

use nom::{ digit, multispace, IResult, not_line_ending } ;

use typ::{ Type, Bool, Int, Rat } ;
use cst::Cst ;
use term::{ CstMaker, Operator } ;


/// Used in tests for parsers.
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
          println!("| done: {}", $res) ;
          $b
        },
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



/// A span indicates a position (new lines count as regular characters).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Spn {
  /// Start of the span.
  pub bgn: usize,
  /// End of the span.
  pub end: usize,
}
impl Spn {
  /// Creates a new span.
  #[inline]
  pub fn mk(bgn: usize, end: usize) -> Self {
    debug_assert!( bgn <= end ) ;
    Spn { bgn: bgn, end: end }
  }
  /// Creates a dummy span.
  #[inline]
  pub fn dummy() -> Self {
    Self::mk(0, 0)
  }
  /// Length of a span.
  #[inline]
  pub fn len(& self) -> usize {
    self.end - self.bgn
  }
}

/// Wraps a span around something.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Spnd<T> {
  /// Something.
  pub val: T,
  /// Spn.
  pub span: Spn,
}
impl<T> Spnd<T> {
  /// Wraps a span around something.
  #[inline]
  pub fn mk(val: T, span: Spn) -> Self {
    Spnd { val: val, span: span }
  }
  /// Wraps a span around something from an offset and a length.
  #[inline]
  pub fn len_mk(val: T, bgn: usize, len: usize) -> Self {
    Self::mk(val, Spn::mk(bgn, bgn + len - 1))
  }
  /// Wraps a span around something from an offset and a length.
  #[inline]
  pub fn bytes_mk(val: T, bgn: usize, bytes: Bytes) -> Self {
    Self::len_mk(val, bgn, bytes.len())
  }
}
impl<T> Deref for Spnd<T> {
  type Target = T ;
  fn deref(& self) -> & T { & self.val }
}
impl<T> DerefMut for Spnd<T> {
  fn deref_mut(& mut self) -> & mut T { & mut self.val }
}

/// Bytes the parser handles.
pub type Bytes<'a> = & 'a [u8] ;

/// Special macro to create parsers.
///
/// Typically used to pass an offset as parameter and returned a `Spnd`
/// thing.
#[macro_export]
macro_rules! mk_parser {
  (
    $(#[$attr:meta])*
    pub fn $id:ident(
      $bytes:ident $(, $param:ident : $param_ty:ty)* $(,)*
    ) -> $out:ty $b:block
  ) => (
    $(#[$attr])*
    pub fn $id(
      $bytes: $crate::parsing::Bytes, $($param: $param_ty),*
    ) -> ::nom::IResult<$crate::parsing::Bytes, $out> $b
  ) ;
  (
    $(#[$attr:meta])*
    fn $id:ident(
      $bytes:ident $(, $param:ident : $param_ty:ty)* $(,)*
    ) -> $out:ty $b:block
  ) => (
    $(#[$attr])*
    fn $id(
      $bytes: $crate::parsing::Bytes, $($param: $param_ty),*
    ) -> nom::IResult<$crate::parsing::Bytes, $out> $b
  ) ;
}

pub mod vmt ;
pub mod smt2 ;

mk_parser!{
  #[doc = "Spanned type parser."]
  pub fn type_parser(bytes, offset: usize) -> Spnd<Type> {
    alt!(
      bytes,
      map!(
        tag!("Int"),  |bytes: Bytes| Spnd::bytes_mk(Type::Int,  offset, bytes)
      ) | map!(
        tag!("Bool"), |bytes: Bytes| Spnd::bytes_mk(Type::Bool, offset, bytes)
      ) | map!(
        tag!("Real"), |bytes: Bytes| Spnd::bytes_mk(Type::Rat,  offset, bytes)
      )
    )
  }
}

named_attr!{
  #[doc = "Parses a line comment."],
  comment<usize>,
  do_parse!(
    char!(';') >>
    line: not_line_ending >>
    (line.len() + 1)
  )
}

mk_parser!{
  #[doc = "Parses spaces and comments. Returns the number of bytes parsed."]
  pub fn space_comment(bytes) -> usize {
    let mut cnt = 0 ;
    map!(
      bytes,
      many0!(
        alt!(
          map!( comment, |n| cnt += n ) |
          map!( multispace, |bytes: & [u8]| cnt += bytes.len() )
        )
      ), |_| cnt
    )
  }
}


named!{ pub bool_parser<Bool>,
  alt!(
    map!( tag!("true"), |_| true ) |
    map!( tag!("false"), |_| false )
  )
}

named!{ pub int_parser<Int>,
  alt!(
    map_opt!(
      do_parse!(
        peek!( one_of!("0123456789") ) >>
        bytes: digit >>
        (bytes)
      ), |bytes| Int::parse_bytes(bytes, 10)
    ) |
    do_parse!(
      char!('(') >>
      opt!(space_comment) >>
      char!('-') >>
      space_comment >>
      int: int_parser >>
      opt!(space_comment) >>
      char!(')') >>
      (- int)
    )
  )
}

named!{ pub rat_parser<Rat>,
  alt!(
    do_parse!(
      peek!( one_of!("0123456789") ) >>
      lft: digit >>
      char!('.') >>
      peek!( one_of!("0123456789") ) >>
      rgt: digit >> ({
        use std::char ;
        let mut num = String::with_capacity(lft.len() + rgt.len()) ;
        let mut den = String::with_capacity(rgt.len() + 1) ;
        den.push('1') ;
        for digit in lft {
          let digit = char::from_u32(* digit as u32).unwrap() ;
          num.push(digit)
        } ;
        for digit in rgt {
          let digit = char::from_u32(* digit as u32).unwrap() ;
          num.push(digit) ;
          den.push('0')
        } ;
        Rat::new(
          Int::parse_bytes(num.as_bytes(), 10).unwrap(),
          Int::parse_bytes(den.as_bytes(), 10).unwrap(),
        )
      })
    ) |
    do_parse!(
      char!('(') >>
      opt!(space_comment) >>
      char!('/') >>
      space_comment >>
      num: int_parser >>
      space_comment >>
      den: int_parser >>
      opt!(space_comment) >>
      char!(')') >> (
        // Unchecked division by 0.
        Rat::new(num, den)
      )
    ) |
    do_parse!(
      char!('(') >>
      opt!(space_comment) >>
      char!('/') >>
      space_comment >>
      num: rat_parser >>
      space_comment >>
      den: rat_parser >>
      opt!(space_comment) >>
      char!(')') >> (
        num / den
      )
    ) |
    do_parse!(
      char!('(') >>
      opt!(space_comment) >>
      char!('-') >>
      space_comment >>
      rat: rat_parser >>
      opt!(space_comment) >>
      char!(')') >> (
        - rat
      )
    )
  )
}

pub fn cst_parser<'a, F>(
  bytes: & 'a [u8], f: & F
) -> IResult<& 'a [u8], Cst>
where F: CstMaker<Bool, Cst> + CstMaker<Int, Cst> + CstMaker<Rat, Cst> {
  preceded!(
    bytes,
    opt!(space_comment),
    alt!(
      map!( int_parser, |i| f.cst(i) ) |
      map!( rat_parser, |r| f.cst(r) ) |
      map!( bool_parser, |b| f.cst(b) )
    )
  )
}

named_attr!{
  #[doc = "Matches the head of a simple symbol."],
  pub simple_symbol_head<char>,
  one_of!("\
    _\
    abcdefghijklmnopqrstuvwxyz\
    ABCDEFGHIJKLMNOPQRSTUVWXYZ\
    ~!$%^&*_-+=<>.?/\
  ")
}

named_attr!{
  #[doc = "Matches the tail of a simple symbol."],
  pub simple_symbol_tail,
  is_a!("\
    _\
    0123456789\
    abcdefghijklmnopqrstuvwxyz\
    ABCDEFGHIJKLMNOPQRSTUVWXYZ\
    ~!@$%^&*_-+=<>.?/\
  ")
}



named_attr!{
  #[doc = "Parses an operator."],
  pub operator_parser<Operator>,
  alt!(
    map!( tag!("=>"), |_| Operator::Impl ) |
    map!( tag!("="), |_| Operator::Eq ) |
    map!( tag!("ite"), |_| Operator::Ite ) |
    map!( tag!("not"), |_| Operator::Not ) |
    map!( tag!("and"), |_| Operator::And ) |
    map!( tag!("or"), |_| Operator::Or ) |
    map!( tag!("xor"), |_| Operator::Xor ) |
    map!( tag!("distinct"), |_| Operator::Distinct ) |
    map!( tag!("+"), |_| Operator::Add ) |
    map!( tag!("-"), |_| Operator::Sub ) |
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

named_attr!{
  #[doc = "Parses a quantifier."],
  quantifier_parser<Quantifier>,
  alt!(
    map!( tag!("forall"), |_| Quantifier::Forall ) |
    map!( tag!("exists"), |_| Quantifier::Exists )
  )
}







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
      |bytes| type_parser(bytes, 0), b"Bool",
      Spnd::len_mk(::typ::Type::Bool, 0, 4)
    )
  }
  #[test]
  fn int() {
    use super::* ;
    try_parse_val!(
      |bytes| type_parser(bytes, 0), b"Int",
      Spnd::len_mk(::typ::Type::Int, 0, 3)
    )
  }
  #[test]
  fn rat() {
    use super::* ;
    try_parse_val!(
      |bytes| type_parser(bytes, 0), b"Real",
      Spnd::len_mk(::typ::Type::Rat, 0, 4)
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
  #[test]
  fn empty() {
    use super::* ;
    match int_parser(& b""[..]) {
      ::nom::IResult::Incomplete(_) => (),
      other => panic!("unexpected result on parsing empty string: {:?}", other)
    } ;
    ()
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
    ) ;
    try_parse_val!(
      rat_parser, b"42.76453",
      Rat::new(
        Int::from_str("4276453").unwrap(),
        Int::from_str("100000").unwrap()
      )
    ) ;
    try_parse_val!(
      rat_parser, b"0.0",
      Rat::new(
        Int::from_str("0").unwrap(),
        Int::from_str("1").unwrap()
      )
    ) ;
    try_parse_val!(
      rat_parser, b"(/ 42.76453 1.0)",
      Rat::new(
        Int::from_str("4276453").unwrap(),
        Int::from_str("100000").unwrap()
      )
    ) ;
    try_parse_val!(
      rat_parser, b"(- (/ 42.76453 1.0))",
      Rat::new(
        Int::from_str("-4276453").unwrap(),
        Int::from_str("100000").unwrap()
      )
    ) ;
    ()
  }
}