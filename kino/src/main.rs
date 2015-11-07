extern crate ansi_term as ansi ;
extern crate term ;
extern crate system as sys ;

use sys::ctxt::* ;

fn main() {
  use std::fs::File ;
  use std::env::args ;

  let bold = ansi::Style::new().bold() ;
  let success_style = ansi::Colour::Green ;
  let success = success_style.paint("success") ;
  let error_style = ansi::Colour::Red.bold() ;
  let error = error_style.paint("error") ;

  fn print_trailer_3() { println!("|===|") }

  println!("") ;
  println!("") ;

  let mut args = args() ;
  args.next().unwrap() ;

  for file in args {
    let factory = term::Factory::mk() ;
    let mut context = Context::mk(factory, 10000) ;

    println!("|===| {} \"{}\"", bold.paint("opening"), file) ;
    match File::open(& file) {
      Ok(mut f) => {
        println!("| {}", success) ;
        println!("|===| {}", bold.paint("parsing")) ;
        match context.read(& mut f) {
          Ok(res) => {
            println!("| {}", success) ;
            print_trailer_3() ;
            println!("") ;
            println!("|===| {}:", bold.paint("Context")) ;
            for line in context.lines().lines() {
              println!("| {}", line)
            } ;
            print_trailer_3() ;
            println!("") ;
            println!("|===| {}:", bold.paint("Outcome")) ;
            for line in res.lines().lines() {
              println!("| {}", line)
            } ;
            println!("|===|")
          },
          Err( e ) => {
            println!("|===| {}", error) ;
            for line in ( format!("{}", e) ).lines() {
              println!("    {} {}", error_style.paint("|"), line)
            } ;
            print_trailer_3()
          },
        }
      },
      Err(e) => {
        println!("|===| {}", error) ;
        for line in ( format!("{}", e) ).lines() {
          println!("    {} {}", error_style.paint("|"), line)
        } ;
        print_trailer_3()
      },
    } ;
    println!("") ;
    println!("") ;
  }
  ()
}
