/*! Parsers for answers to SMT Lib 2.5 queries. */

use ::std::str ;

use ::nom::multispace ;

use ::base::{
  Offset, bytes_to_offset
} ;

use super::{
  simple_symbol_head, simple_symbol_tail,
} ;

named!{ offset<Offset>,
  chain!(
    char!('@') ~
    offset: is_a!("0123456789"),
    || bytes_to_offset(offset)
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
        sym: map!(
          is_not!("|\\"),
          |bytes| String::from(
            str::from_utf8(bytes).unwrap()
          )
        ),
        || (sym, offset)
      ),
      char!('|')
    )
  )
}

