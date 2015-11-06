#![allow(non_upper_case_globals)]

#[macro_use]
extern crate nom ;
extern crate term ;

use std::io::Read ;

mod base ;
pub use base::{
  Sig, Args, Uf, Fun, Prop, Sys
} ;

mod parse ;

/** Reads and remembers what has been read. */
pub mod ctxt {
  pub use super::base::Callable ;
  pub use super::parse::{
    Res, Context
  } ;
  pub use super::parse::check::Error ;

}

fn main() {
  use std::fs::File ;
  use std::env::args ;

  println!("") ;
  println!("") ;
  println!("|===| Greetings.") ;
  println!("") ;
  println!("") ;

  let mut args = args() ;
  args.next().unwrap() ;

  for file in args {
    let factory = term::Factory::mk() ;
    let mut context = parse::Context::mk(factory, 10000) ;

    println!("opening \"{}\"", file) ;
    match File::open(& file) {
      Ok(mut f) => {
        print!("parsing ... ") ;
        match context.read(& mut f) {
          Ok(res) => {
            println!("done") ;
            println!("") ;
            println!("|===| Context:") ;
            for line in context.lines().lines() {
              println!("| {}", line)
            } ;
            println!("|===|\n\n|===| Outcome:") ;
            for line in res.lines().lines() {
              println!("| {}", line)
            } ;
            println!("|===|")
          },
          Err( e ) => {
            println!("error") ;
            println!("> {}", e)
          },
        }
      },
      Err(e) => println!("error\n  {}", e),
    } ;
    println!("") ;
    println!("") ;
  }
  ()
}