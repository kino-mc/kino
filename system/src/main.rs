#[macro_use]
extern crate nom ;
extern crate term ;

use std::io::Read ;

mod parse ;
use parse::Res ;

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
          Ok( Res::Exit ) => println!("got exit"),
          Ok( Res::Check(sys, props) ) => {
            println!("done") ;
            println!("") ;
            println!("") ;
            context.stdin_print() ;
            println!("") ;
            println!("got a check") ;
            println!("| sys: \"{}\"", sys) ;
            println!("| props:") ;
            for prop in props.iter() { println!("  {}", prop) } ;
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