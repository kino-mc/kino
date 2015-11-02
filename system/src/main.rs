#[macro_use]
extern crate nom ;
extern crate term ;

use std::io::{ Read, BufRead } ;

pub mod base ;
pub mod parse ;

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
    let mut context = base::Context::mk(factory, 10000) ;

    println!("opening \"{}\"", file) ;
    match File::open(& file) {
      Ok(mut f) => {
        println!("parsing...") ;
        match context.read(& mut f) {
          Ok( Ok(None) ) => println!("got exit"),
          Ok( Ok( Some( (sys, props, cands) ) ) ) => {
            println!("...done") ;
            println!("") ;
            println!("") ;
            println!("Context:") ;
            for line in context.lines().lines() {
              println!("| {}", line)
            } ;
            println!("") ;
            println!("got a check") ;
            println!("| sys: \"{}\"", sys) ;
            println!("| props:") ;
            for prop in props.iter() { println!("    {}", prop) } ;
            println!("| cands:") ;
            for cand in cands.iter() { println!("    {}", cand) } ;
          },
          Ok( Err( (i1, i2) ) ) => {
            println!("parse error: multiple definition for same symbol:") ;
            println!(" first {:?}", i2) ;
            println!(" then  {:?}", i1) ;
          },
          Err(e) => println!("io error: {}", e),
        }
      },
      Err(e) => println!("error: {}", e),
    } ;
    println!("") ;
    println!("") ;
  }
  ()
}