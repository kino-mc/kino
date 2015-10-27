/** Parsers and such. */

use ::std::str ;

use ::nom::multispace ;

use ::typ::{ Bool, Int, Rat } ;
use ::term::State ;

named!{ state<State>,
  alt!(
    map!( tag!("@0"), |_| State::Zero ) |
    map!( tag!("@1"), |_| State::One  )
  )
}

/** Matches the head of a simple symbol. */
named!{ simple_symbol_head<char>,
  one_of!("\
    _\
    abcdefghijklmnopqrstuvwxyz\
    ABCDEFGHIJKLMNOPQRSTUVWXYZ\
    ~!$%^&*_-+=<>.?/
  ")
}

/** Matches the tail of a simple symbol. */
named!{ simple_symbol_tail,
  is_a!("\
    _\
    0123456789\
    abcdefghijklmnopqrstuvwxyz\
    ABCDEFGHIJKLMNOPQRSTUVWXYZ\
    ~!$%^&*_-+=<>.?/
  ")
}

named!{ pub id_parser< (String, Option<State>) >,
  alt!(
    // Simple symbol.
    chain!(
      head: simple_symbol_head ~
      tail: simple_symbol_tail ~
      state: opt!(state),
      || (
        format!("{}{}", head, str::from_utf8(tail).unwrap()),
        state
      )
    ) |
    // Quoted symbol.
    delimited!(
      char!('|'),
      chain!(
        sym: map!(
          is_not!("|\\@"),
          |bytes| String::from(
            str::from_utf8(bytes).unwrap()
          )
        ) ~
        state: opt!(state),
        || (sym, state)
      ),
      char!('|')
    )
  )
}


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