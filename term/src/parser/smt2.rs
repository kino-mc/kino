// Copyright 2015 Adrien Champion. See the COPYRIGHT file at the top-level
// directory of this distribution.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

/*! Parsers for answers to SMT Lib 2.5 queries. */

use ::std::str ;

use ::nom::multispace ;

use ::base::Offset ;

use super::{
  simple_symbol_head, simple_symbol_tail,
} ;

named!{ offset<Offset>,
  chain!(
    char!('@') ~
    offset: is_a!("0123456789"),
    || Offset::of_bytes(offset)
  )
}

named!{ pub id_parser< (String, Option<Offset>) >,
  alt!(
    // Simple symbol.
    chain!(
      offset: opt!(offset) ~
      head: simple_symbol_head ~
      tail: simple_symbol_tail,
      || (
        format!("{}{}", head, str::from_utf8(tail).unwrap()),
        offset
      )
    ) |
    // Quoted symbol.
    delimited!(
      char!('|'),
      chain!(
        offset: opt!(offset) ~
        head: none_of!("|\\@") ~
        sym: map!(
          is_not!("|\\"), str::from_utf8
        ),
        || ( format!("{}{}", head, sym.unwrap()), offset )
      ),
      char!('|')
    )
  )
}












#[cfg(test)]
macro_rules! try_parse_id {
  ($fun:expr, $arg:expr, $state:expr, $id:expr) => (
    try_parse!($fun, $arg,
      (s, res) -> {
        let (id, state) = res ;
        let exp: Option<Offset> = $state ;
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
mod simpl_sym {
  use base::Offset ;
  #[test]
  fn nsvar() {
    use super::* ;
    try_parse_id!(id_parser, b"bla", None, "bla") ;
    try_parse_id!(id_parser, b"_bla!52740>^^&", None, "_bla!52740>^^&") ;
  }
  #[test]
  fn svar() {
    use super::* ;
    try_parse_id!(id_parser, b"@7bla", Some(Offset::of_int(7)), "bla") ;
    try_parse_id!(
      id_parser, b"@42!52@_740>^^&",
      Some(Offset::of_int(42)), "!52@_740>^^&"
    ) ;
  }
}

#[cfg(test)]
mod quoted_sym {
  use base::Offset ;
  #[test]
  fn nsvar() {
    use super::* ;
    try_parse_id!(id_parser, b"|bla|", None, "bla") ;
    try_parse_id!(
      id_parser, b"|[{}_b}(l=a}(!**52)740>^^&|",
      None, "[{}_b}(l=a}(!**52)740>^^&"
    ) ;
  }
  #[test]
  fn svar() {
    use super::* ;
    try_parse_id!(id_parser, b"|@7bla|", Some(Offset::of_int(7)), "bla") ;
    try_parse_id!(
      id_parser, b"|@42[{!+)*(![{}+=*!/~%75!52@_740>^^&|",
      Some(Offset::of_int(42)), "[{!+)*(![{}+=*!/~%75!52@_740>^^&"
    ) ;
  }
}