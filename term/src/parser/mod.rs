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
use std::fmt ;
use std::io::Write ;

use nom::{ digit, multispace, IResult, not_line_ending } ;

use typ::{ Type, Bool, Int, Rat } ;
use cst::Cst ;
use term::{ CstMaker, Operator } ;
use rsmt2::{ Sort2Smt, Sym2Smt, Expr2Smt } ;
use rsmt2::errors::Res ;


/// Used in tests for parsers.
#[cfg(test)]
macro_rules! try_parse {
  (
    $fun:expr, $factory:expr, $arg:expr,
    ($s:ident, $res:ident) -> $b:block
  ) => (
    {
      let $s = ::std::str::from_utf8($arg).unwrap() ;
      println!("| parsing `{}`", $s) ;
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
      println!("| parsing `{}`", $s) ;
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
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
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
  /// Creates a new span from an offset and a length.
  #[inline]
  pub fn len_mk(bgn: usize, len: usize) -> Self {
    debug_assert!( len > 0 ) ;
    Spn::mk(bgn, bgn + len - 1)
  }
  /// Creates a dummy span.
  #[inline]
  pub fn dummy() -> Self {
    Self::mk(0, 0)
  }
  /// Length of a span.
  #[inline]
  pub fn len(& self) -> usize {
    self.end - self.bgn + 1
  }
}
impl fmt::Display for Spn {
  fn fmt(& self, fmt: & mut fmt::Formatter) -> fmt::Result {
    write!(fmt, "[{}-{}]", self.bgn, self.end)
  }
}

/// Wraps a span around something.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
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
  /// Accessor for the value stored.
  #[inline]
  pub fn get(& self) -> & T {
    & self.val
  }
  /// Wraps a span around something from an offset and a length.
  #[inline]
  pub fn len_mk(val: T, bgn: usize, len: usize) -> Self {
    Self::mk(val, Spn::len_mk(bgn, len))
  }
  /// Wraps a span around something from an offset and a length.
  #[inline]
  pub fn bytes_mk(val: T, bgn: usize, bytes: Bytes) -> Self {
    Self::len_mk(val, bgn, bytes.len())
  }
  /// Length of a span.
  #[inline]
  pub fn len(& self) -> usize {
    self.span.len()
  }
  /// Map over a spanned thing.
  #[inline]
  pub fn map<U, F: Fn(T) -> U>(self, f: F) -> Spnd<U> {
    Spnd { val: f(self.val), span: self.span }
  }
  /// Destroys a `Spnd`.
  #[inline]
  pub fn destroy(self) -> (T, Spn) { (self.val, self.span) }
  /// Destroys a `Spnd`, returning its span.
  #[inline]
  pub fn to_span(self) -> Spn { self.destroy().1 }
}
impl<T: Clone> Spnd<T> {
  /// Same as `destroy` but does not eats a `self`.
  #[inline]
  pub fn extract(& self) -> (T, Spn) { (self.val.clone(), self.span.clone()) }
}
impl<T> Deref for Spnd<T> {
  type Target = T ;
  fn deref(& self) -> & T { & self.val }
}
impl<T> DerefMut for Spnd<T> {
  fn deref_mut(& mut self) -> & mut T { & mut self.val }
}
impl<T: fmt::Display> fmt::Display for Spnd<T> {
  fn fmt(& self, fmt: & mut fmt::Formatter) -> fmt::Result {
    write!(fmt, "{}{}", self.val, self.span)
  }
}
impl<Info, T: Expr2Smt<Info>> Expr2Smt<Info> for Spnd<T> {
  fn expr_to_smt2(& self, writer: & mut Write, info: & Info) -> Res<()> {
    self.val.expr_to_smt2(writer, info)
  }
}
impl<T: Sort2Smt> Sort2Smt for Spnd<T> {
  fn sort_to_smt2(& self, writer: & mut Write) -> Res<()> {
    self.val.sort_to_smt2(writer)
  }
}
impl<Info, T: Sym2Smt<Info>> Sym2Smt<Info> for Spnd<T> {
  fn sym_to_smt2(& self, writer: & mut Write, info: & Info) -> Res<()> {
    self.val.sym_to_smt2(writer, info)
  }
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

/// Adds the span of a sub-parser.
#[macro_export]
macro_rules! len_add {
  ($bytes:expr, $len:ident < char $c:expr) => (
    map!($bytes, char!($c), |_| $len += 1)
  ) ;
  ($bytes:expr, $len:ident < tag $c:expr) => (
    map!($bytes, tag!($c), |bytes: & [u8]| $len += bytes.len())
  ) ;
  ($bytes:expr, $len:ident < tag spn($offset:expr) $c:expr) => (
    map!(
      $bytes, tag!($c), |bytes: & [u8]| {
        $len += bytes.len() ;
        $crate::parsing::Spn::len_mk($offset, bytes.len())
      }
    )
  ) ;
  ($byte:expr, $len:ident < spc cmt) => (
    len_add!($byte, $len < int space_comment)
  ) ;
  ($byte:expr, $len:ident < opt spc cmt) => (
    opt!($byte, len_add!($len < spc cmt) )
  ) ;
  ($bytes:expr, $len:ident < bytes $submac:ident!( $($args:tt)* )) => (
    map!(
      $bytes,
      $submac!($($args)*),
      |stuff: & [u8]| $len += stuff.len()
    )
  ) ;
  ($bytes:expr, $len:ident < int $submac:ident!( $($args:tt)* )) => (
    map!(
      $bytes,
      $submac!($($args)*),
      |int| $len += int
    )
  ) ;
  ($bytes:expr, $len:ident < spn thru $submac:ident!( $($args:tt)* )) => (
    map!(
      $bytes,
      $submac!($($args)*),
      |stuff| {
        $len += $crate::parsing::Spnd::len(& stuff) ;
        stuff
      }
    )
  ) ;
  ($bytes:expr, $len:ident < spn $submac:ident!( $($args:tt)* )) => (
    map!(
      $bytes,
      $submac!($($args)*),
      |stuff| {
        let (stuff, span) = $crate::parsing::Spnd::destroy(stuff) ;
        $len += span.len() ;
        stuff
      }
    )
  ) ;
  ($bytes:expr, $len:ident < trm $submac:ident!( $($args:tt)* )) => (
    map!(
      $bytes,
      $submac!($($args)*),
      |term: $crate::parsing::TermAndDep| {
        $len += term.span.len() ;
        term
      }
    )
  ) ;
  ($bytes:expr, $len:ident < bytes $parser:expr) => (
    map!(
      $bytes,
      call!($parser),
      |stuff: & [u8]| $len += stuff.len()
    )
  ) ;
  ($bytes:expr, $len:ident < int $parser:expr) => (
    map!(
      $bytes,
      call!($parser),
      |int| $len += int
    )
  ) ;
  ($bytes:expr, $len:ident < spn $parser:expr) => (
    map!(
      $bytes,
      call!($parser),
      |stuff| {
        let (stuff, span) = $crate::parsing::Spnd::destroy(stuff) ;
        $len += span.len() ;
        stuff
      }
    )
  ) ;
  ($bytes:expr, $len:ident < trm $parser:expr) => (
    map!(
      $bytes,
      call!($parser),
      |term: $crate::parsing::TermAndDep| {
        $len += term.span.len() ;
        term
      }
    )
  ) ;
}

/// Adds the span of a sub-parser.
#[macro_export]
macro_rules! len_set {
  ($bytes:expr, $len:ident < char $c:expr) => (
    map!($bytes, char!($c), |_| $len = 1)
  ) ;
  ($byte:expr, $len:ident < spc cmt) => (
    len_set!($byte, $len < int space_comment)
  ) ;
  ($byte:expr, $len:ident < opt spc cmt) => (
    opt!($byte, len_set!($len < spc cmt) )
  ) ;
  ($bytes:expr, $len:ident < len $submac:ident!( $($args:tt)* )) => (
    map!(
      $bytes,
      $submac!($($args)*),
      |stuff| { $len = stuff.len() ; stuff }
    )
  ) ;
  ($bytes:expr, $len:ident < int $submac:ident!( $($args:tt)* )) => (
    map!(
      $bytes,
      $submac!($($args)*),
      |int| { $len = int ; int }
    )
  ) ;
  ($bytes:expr, $len:ident < spn $submac:ident!( $($args:tt)* )) => (
    map!(
      $bytes,
      $submac!($($args)*), |stuff| {
        let (stuff, span) = $crate::parsing::Spnd::destroy(stuff) ;
        $len = span.len() ;
        stuff
      }
    )
  ) ;
  ($bytes:expr, $len:ident < spn thru $submac:ident!( $($args:tt)* )) => (
    map!(
      $bytes,
      $submac!($($args)*), |stuff| {
        $len += $crate::parsing::Spnd::len(& stuff) ;
        stuff
      }
    )
  ) ;
  ($bytes:expr, $len:ident < trm $submac:ident!( $($args:tt)* )) => (
    map!(
      $bytes,
      $submac!($($args)*), |term: $crate::parsing::TermAndDep| {
        $len = term.span.len() ;
        term
      }
    )
  ) ;
  ($bytes:expr, $len:ident < len $parser:expr) => (
    map!(
      $bytes,
      call!($parser),
      |stuff| { $len = stuff.len() ; stuff }
    )
  ) ;
  ($bytes:expr, $len:ident < int $parser:expr) => (
    map!(
      $bytes,
      call!($parser),
      |int| { $len = int ; int }
    )
  ) ;
  ($bytes:expr, $len:ident < spn $parser:expr) => (
    map!(
      $bytes,
      call!($parser),
      |stuff| {
        let (stuff, span) = $crate::parsing::Spnd::destroy(stuff) ;
        $len = span.len() ;
        stuff
      }
    )
  ) ;
  ($bytes:expr, $len:ident < spn thru $parser:expr) => (
    map!(
      $bytes,
      call!($parser),|stuff| {
        $len += $crate::parsing::Spnd::len(& stuff) ;
        stuff
      }
    )
  ) ;
  ($bytes:expr, $len:ident < trm $parser:expr) => (
    map!(
      $bytes,
      call!($parser),
      |term: $crate::parsing::TermAndDep| {
        $len = term.span.len() ;
        term
      }
    )
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
  #[doc = "Parses a line comment, returns the number of bytes parsed."],
  pub comment<usize>,
  do_parse!(
    char!(';') >>
    line: not_line_ending >>
    (line.len() + 1)
  )
}

mk_parser!{
  #[doc = "Parses spaces and comments, returns the number of bytes parsed."]
  pub fn space_comment(bytes) -> usize {
    let mut len = 0 ;
    map!(
      bytes,
      many0!(
        alt!(
          len_add!(len < int comment) |
          len_add!(len < bytes multispace)
        )
      ), |_| len
    )
  }
}


mk_parser!{
  #[doc = "Parses a spanned bool constant."]
  pub fn bool_parser(bytes, offset: usize) -> Spnd<Bool> {
    alt!(
      bytes,
      map!(
        tag!("true"),
        |bytes| Spnd::bytes_mk(true, offset, bytes)
      ) |
      map!(
        tag!("false"),
        |bytes| Spnd::bytes_mk(false, offset, bytes)
      )
    )
  }
}

mk_parser!{
  #[doc = "Parses a spanned int constant."]
  pub fn int_parser(bytes, offset: usize) -> Spnd<Int> {
    let mut len = 0 ;
    alt!(
      bytes,
      map!(
        map_opt!(
          do_parse!(
            peek!( one_of!("0123456789") ) >>
            bytes: digit >>
            (bytes)
          ), |bytes: Bytes| {
            len = bytes.len() ;
            Int::parse_bytes(bytes, 10)
          }
        ), |int| Spnd::len_mk(int, offset, len)
      ) |
      do_parse!(
        len_set!(len < char '(') >>
        opt!( len_add!(len < int space_comment) ) >>
        len_add!(len < char '-' ) >>
        len_add!(len < int space_comment) >>
        int: len_add!(
          len < spn apply!(int_parser, offset + len)
        ) >>
        opt!( len_add!(len < int space_comment) ) >>
        len_add!(len < char ')') >> ({
          Spnd::len_mk(- int, offset, len)
        })
      )
    )
  }
}

mk_parser!{
  #[doc = "Parses a spanned rational constant."]
  pub fn rat_parser(bytes, offset: usize) -> Spnd<Rat> {
    let mut len = 0 ;
    alt!(
      bytes,
      do_parse!(
        peek!( one_of!("0123456789") ) >>
        lft: digit >>
        len_add!(len < char '.') >>
        peek!( one_of!("0123456789") ) >>
        rgt: digit >> ({
          use std::char ;
          len += lft.len() ;
          len += rgt.len() ;
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
          Spnd::len_mk(
            Rat::new(
              Int::parse_bytes(num.as_bytes(), 10).unwrap(),
              Int::parse_bytes(den.as_bytes(), 10).unwrap(),
            ), offset, len
          )
        })
      ) |
      do_parse!(
        len_set!(len < char '(') >>
        opt!( len_add!(len < int space_comment) ) >>
        len_add!(len < char '/') >>
        len_add!(len < int space_comment) >>
        num: len_add!(
          len < spn apply!(int_parser, offset + len)
        ) >>
        len_add!(len < int space_comment) >>
        den: len_add!(
          len < spn apply!(int_parser, offset + len)
        ) >>
        opt!( len_add!(len < int space_comment) ) >>
        len_add!(len < char ')') >> (
          // Unchecked division by 0.
          Spnd::len_mk(
            Rat::new(num, den), offset, len
          )
        )
      ) |
      do_parse!(
        len_set!(len < char '(') >>
        opt!( len_add!(len < int space_comment) ) >>
        len_add!(len < char '/') >>
        len_add!(len < int space_comment) >>
        num: len_add!(
          len < spn apply!(rat_parser, offset + len)
        ) >>
        len_add!(len < int space_comment) >>
        den: len_add!(
          len < spn apply!(rat_parser, offset + len)
        ) >>
        opt!( len_add!(len < int space_comment) ) >>
        len_add!(len < char ')') >> (
          Spnd::len_mk(
            num / den, offset, len
          )
        )
      ) |
      do_parse!(
        len_set!(len < char '(') >>
        opt!( len_add!(len < int space_comment) ) >>
        len_add!(len < char '-') >>
        len_add!(len < int space_comment) >>
        rat: len_add!(
          len < spn apply!(rat_parser, offset + len)
        ) >>
        opt!( len_add!(len < int space_comment) ) >>
        len_add!(len < char ')') >> (
          Spnd::len_mk(
            - rat, offset, len
          )
        )
      )
    )
  }
}

pub fn cst_parser<'a, F>(
  bytes: & 'a [u8], offset: usize, f: & F
) -> IResult<& 'a [u8], Spnd<Cst>>
where F: CstMaker<Bool, Cst> + CstMaker<Int, Cst> + CstMaker<Rat, Cst> {
  let mut len = 0 ;
  preceded!(
    bytes,
    opt!( len_add!(len < int space_comment) ),
    alt_complete!(
      map!(
        apply!(rat_parser, offset),  |r:Spnd<Rat>| r.map(|r| f.cst(r))
      ) |
      map!(
        apply!(int_parser, offset),  |i:Spnd<Int>| i.map(|i| f.cst(i))
      ) |
      map!(
        apply!(bool_parser, offset), |b:Spnd<Bool>| b.map(|b| f.cst(b))
      )
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


mk_parser!{
  #[doc = "Parses an operator."]
  pub fn operator_parser(bytes, offset: usize) -> Spnd<Operator> {
    alt!(
      bytes,
      map!(
        tag!("=>"),
        |b: Bytes| Spnd::len_mk(Operator::Impl, offset, b.len())
      ) |
      map!(
        tag!("="),
        |b: Bytes| Spnd::len_mk(Operator::Eq, offset, b.len())
      ) |
      map!(
        tag!("ite"),
        |b: Bytes| Spnd::len_mk(Operator::Ite, offset, b.len())
      ) |
      map!(
        tag!("not"),
        |b: Bytes| Spnd::len_mk(Operator::Not, offset, b.len())
      ) |
      map!(
        tag!("and"),
        |b: Bytes| Spnd::len_mk(Operator::And, offset, b.len())
      ) |
      map!(
        tag!("or"),
        |b: Bytes| Spnd::len_mk(Operator::Or, offset, b.len())
      ) |
      map!(
        tag!("xor"),
        |b: Bytes| Spnd::len_mk(Operator::Xor, offset, b.len())
      ) |
      map!(
        tag!("distinct"),
        |b: Bytes| Spnd::len_mk(Operator::Distinct, offset, b.len())
      ) |
      map!(
        tag!("+"),
        |b: Bytes| Spnd::len_mk(Operator::Add, offset, b.len())
      ) |
      map!(
        tag!("-"),
        |b: Bytes| Spnd::len_mk(Operator::Sub, offset, b.len())
      ) |
      map!(
        tag!("*"),
        |b: Bytes| Spnd::len_mk(Operator::Mul, offset, b.len())
      ) |
      map!(
        tag!("/"),
        |b: Bytes| Spnd::len_mk(Operator::Div, offset, b.len())
      ) |
      map!(
        tag!("<="),
        |b: Bytes| Spnd::len_mk(Operator::Le, offset, b.len())
      ) |
      map!(
        tag!(">="),
        |b: Bytes| Spnd::len_mk(Operator::Ge, offset, b.len())
      ) |
      map!(
        tag!("<"),
        |b: Bytes| Spnd::len_mk(Operator::Lt, offset, b.len())
      ) |
      map!(
        tag!(">"),
        |b: Bytes| Spnd::len_mk(Operator::Gt, offset, b.len())
      )
    )
  }
}

/// A quantifier at parsing time.
pub enum Quantifier {
  /// Universal.
  Forall,
  /// Existential.
  Exists
}

mk_parser!{
  #[doc = "Parses a quantifier."]
  pub fn quantifier_parser(bytes, offset: usize) -> Spnd<Quantifier> {
    alt!(
      bytes,
      map!(
        tag!("forall"),
        |b: Bytes| Spnd::len_mk(Quantifier::Forall, offset, b.len())
      ) |
      map!(
        tag!("exists"),
        |b: Bytes| Spnd::len_mk(Quantifier::Exists, offset, b.len())
      )
    )
  }
}





#[cfg(test)]
macro_rules! try_parse_val {
  ($fun:expr, $arg:expr, $val:expr) => (
    try_parse!($fun, $arg,
      (s, val) -> {
        println!("| expected: `{:?}`", $val) ;
        assert_eq!(val, $val)
      }
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
      |bytes| bool_parser(bytes, 0), b"true",
      Spnd::len_mk(true, 0, 4)
    )
  }
  #[test]
  fn fals3() {
    use super::* ;
    try_parse_val!(
      |bytes| bool_parser(bytes, 0), b"false",
      Spnd::len_mk(false, 0, 5)
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
      |bytes| int_parser(bytes, 0), b"42",
      Spnd::len_mk(
        Int::from_str("42").unwrap(), 0, 2
      )
    ) ;
    try_parse_val!(
      |bytes| int_parser(bytes, 0), b"74205432075342042",
      Spnd::len_mk(
        Int::from_str("74205432075342042").unwrap(), 0, 17
      )
    )
  }
  #[test]
  fn empty() {
    use super::* ;
    match int_parser(& b""[..], 0) {
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
      |bytes| rat_parser(bytes, 0), b"(/ 0 1)",
      Spnd::len_mk(
        Rat::new(
          Int::from_str("0").unwrap(),
          Int::from_str("1").unwrap()
        ), 0, 7
      )
    ) ;
    try_parse_val!(
      |bytes| rat_parser(bytes, 0), b"( / 74205432075342042 76453   )",
      Spnd::len_mk(
        Rat::new(
          Int::from_str("74205432075342042").unwrap(),
          Int::from_str("76453").unwrap()
        ), 0, 31
      )
    ) ;
    try_parse_val!(
      |bytes| rat_parser(bytes, 0), b"42.76453",
      Spnd::len_mk(
        Rat::new(
          Int::from_str("4276453").unwrap(),
          Int::from_str("100000").unwrap()
        ), 0, 8
      )
    ) ;
    try_parse_val!(
      |bytes| rat_parser(bytes, 0), b"0.0",
      Spnd::len_mk(
        Rat::new(
          Int::from_str("0").unwrap(),
          Int::from_str("1").unwrap()
        ), 0, 3
      )
    ) ;
    try_parse_val!(
      |bytes| rat_parser(bytes, 0), b"(/ 42.76453 1.0)",
      Spnd::len_mk(
        Rat::new(
          Int::from_str("4276453").unwrap(),
          Int::from_str("100000").unwrap()
        ), 0, 16
      )
    ) ;
    try_parse_val!(
      |bytes| rat_parser(bytes, 0), b"(- (/ 42.76453 1.0))",
      Spnd::len_mk(
        Rat::new(
          Int::from_str("-4276453").unwrap(),
          Int::from_str("100000").unwrap()
        ), 0, 20
      )
    ) ;
    ()
  }
}