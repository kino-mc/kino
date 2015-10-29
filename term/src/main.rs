extern crate num ;
extern crate hashconsing as hcons ;
#[macro_use]
extern crate nom ;

use std::str ;

use nom::IResult::* ;

mod base ;
pub mod typ ;
pub mod sym ;
pub mod cst ;
pub mod term ;
pub mod parser ;

pub use base::* ;

macro_rules! try_parse {
  ($fun:expr, $arg:expr) => (
    {
      println!(
        "| parsing \"{}\"", str::from_utf8($arg).unwrap()
      ) ;
      match $fun(& $arg[..]) {
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
    parser::smtrans::id_parser, b"next.bla"
  ) ;

  try_parse!(
    parser::smtrans::id_parser, b"bla"
  ) ;

  try_parse!(
    parser::smtrans::id_parser, b"|bsth[)]*]+)!&[{})*])/lnstzvm;,.pyla|"
  ) ;

  try_parse!(
    parser::smtrans::id_parser, b"|state.bsth[)]*]+)!&[{})*])/lnstzvm;,.pyla|"
  ) ;

  println!("") ;
  println!("") ;

  println!("|===| Testing bool parser.") ;
  println!("") ;

  try_parse!(
    parser::bool_parser, b"true"
  ) ;

  try_parse!(
    parser::bool_parser, b"false"
  ) ;

  println!("") ;
  println!("") ;

  println!("|===| Testing int parser.") ;
  println!("") ;

  try_parse!(
    parser::int_parser, b"42"
  ) ;

  try_parse!(
    parser::int_parser, b"450134291675203472056472501627956329765342942"
  ) ;

  println!("") ;
  println!("") ;

  println!("|===| Testing rat parser.") ;
  println!("") ;

  try_parse!(
    parser::rat_parser, b"(/ 42 7)"
  ) ;

  try_parse!(
    parser::rat_parser, b"(/ 42 7)"
  ) ;

  try_parse!(
    parser::rat_parser, b"(/ 427205347 7754237425397059340795023976376)"
  ) ;

  println!("") ;
}