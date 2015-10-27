extern crate num ;
extern crate hashconsing as hcons ;
extern crate regex ;
#[macro_use]
extern crate nom ;

use std::str ;

use nom::IResult::* ;

mod base ;
pub mod typ ;
pub mod sym ;
pub mod id ;
pub mod term ;
pub mod parse ;

pub use base::* ;

macro_rules! try_parse {
  ($fun:expr, $arg:expr) => (
    {
      println!(
        "| parsing \"{}\"", String::from(str::from_utf8($arg).unwrap())
      ) ;
      match $fun($arg) {
        Done(_,out) => println!("| done: {:?}", out),
        Error(e) => panic!("error: {:?}", e),
        Incomplete(n) => panic!("incomplete: {:?}", n),
      } ;
      println!("") ;
    }
  )
}

fn main() {
  println!("") ;
  println!("") ;

  println!("|===| Testing ident parser.") ;
  println!("") ;

  try_parse!(
    parse::id_parser, & b"bla@1"[..]
  ) ;

  try_parse!(
    parse::id_parser, & b"bla"[..]
  ) ;

  try_parse!(
    parse::id_parser, & b"|bsth[)]*]+)!&[{})*])/lnstzvm;,.pyla|"[..]
  ) ;

  try_parse!(
    parse::id_parser, & b"|bsth[)]*]+)!&[{})*])/lnstzvm;,.pyla@0|"[..]
  ) ;

  println!("") ;
  println!("") ;

  println!("|===| Testing bool parser.") ;
  println!("") ;

  try_parse!(
    parse::bool_parser, & b"true"[..]
  ) ;

  try_parse!(
    parse::bool_parser, & b"false"[..]
  ) ;

  println!("") ;
  println!("") ;

  println!("|===| Testing int parser.") ;
  println!("") ;

  try_parse!(
    parse::int_parser, & b"42"[..]
  ) ;

  try_parse!(
    parse::int_parser, & b"450134291675203472056472501627956329765342942"[..]
  ) ;

  println!("") ;
  println!("") ;

  println!("|===| Testing rat parser.") ;
  println!("") ;

  try_parse!(
    parse::rat_parser, & b"(/ 42 7)"[..]
  ) ;

  try_parse!(
    parse::rat_parser, & b"(/ 42 7)"[..]
  ) ;

  try_parse!(
    parse::rat_parser, & b"(/ 427205347 7754237425397059340795023976376)"[..]
  ) ;

  println!("") ;
}