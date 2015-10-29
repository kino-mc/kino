/** Parsers and such. */

use nom::multispace ;

use ::typ::{ Bool, Int, Rat } ;

/** Used in tests for parsers. */
#[cfg(test)]
macro_rules! try_parse {
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

named!{ pub bool_parser<Bool>,
  alt!(
    map!( tag!("true" ), |_| true  ) |
    map!( tag!("false"), |_| false )
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










#[cfg(test)]
macro_rules! try_parse_val {
  ($fun:expr, $arg:expr, $val:expr) => (
    try_parse!($fun, $arg,
      (s, val) -> { assert_eq!(val, $val) }
    )
  ) ;
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