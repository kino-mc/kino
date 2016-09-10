//! Things used by all tests.

use std::fmt ;

pub use kino::PropStatus ;

/// Statuses expected by test functions.
#[allow(dead_code)]
pub enum ExpStatus {
  /// K-true.
  KTru(usize),
  /// Falsified.
  False(usize),
  /// Invariant.
  Inv(usize),
}
impl ExpStatus {
  /// Compares an `ExpStatus` to a `PropStatus`.
  pub fn eq(& self, status: & PropStatus) -> bool {
    use self::ExpStatus::* ;
    use kino::PropStatus::* ;
    match (self, status) {

      (& False(n), & Falsified(ref cex))
      if cex.len() == n => true,

      (& Inv(n), & Invariant(exp_n))
      if n == exp_n => true,

      (& Inv(n), & MinInvariant(exp_n, _))
      if n == exp_n => true,

      (& KTru(n), & KTrue(exp_n))
      if n == exp_n => true,

      _ => false,

    }
  }
}
impl fmt::Display for ExpStatus {
  fn fmt(& self, fmt: & mut fmt::Formatter) -> fmt::Result {
    use self::ExpStatus::* ;
    match * self {
      KTru(n) => write!(fmt, "<{}-true>", n),
      False(n) => write!(fmt, "<{}-false>", n),
      Inv(n) => write!(fmt, "<{}-invariant>", n),
    }
  }
}

/// Tiny DSL for `ExpStatus`.
#[macro_export]
macro_rules! exp {
  (true $n:expr) => ( common::ExpStatus::KTru($n) ) ;
  (false $n:expr) => ( common::ExpStatus::False($n) ) ;
  (inv $n:expr) => ( common::ExpStatus::Inv($n) ) ;
}

/// Test macro, creates a test function for a file expecting some results.
#[macro_export]
macro_rules! mk_test {
  (
    $name:ident, $path:expr $(
      , $prop_sym:expr => $prop_status:expr
    )* ,
  ) => (
    mk_test!{
      $name, $path $(, $prop_sym => $prop_status )*
    }
  ) ;
  (
    $name:ident, $path:expr $(
      , $prop_sym:expr => $prop_status:expr
    )*
  ) => (
    #[test]
    fn $name() {
      #![allow(unused_mut)]
      let file = & $path ;
      match kino::analyze(file) {
        Ok( (context, props) ) => {
          use std::collections::HashMap ;
          use common::ExpStatus ;
          #[allow(unused_imports)]
          use kino::{ SymMaker, PropStatus, Sym } ;
          let mut map = HashMap::<Sym, ExpStatus>::new() ;
          $(
            let prop_sym = context.factory().sym( $prop_sym ) ;
            map.insert( prop_sym, $prop_status ) ;
          )*
          println!("") ;
          println!("") ;
          let mut all_good = true ;
          for prop in props.into_iter() {
            if let Some( & (_, ref status) ) = context.get_prop( prop.sym() ) {
              if let Some(exp_status) = map.get( prop.sym() ) {
                if ! exp_status.eq( status ) {
                  all_good = false ;
                  println!("error on prop `{}`", prop.sym()) ;
                  println!( "  expected {}", exp_status ) ;
                  println!(
                    "       got {}", common::str_of_status(& status)
                  ) ;
                  println!("") ;
                } else {
                  println!("all good on prop `{}`", prop.sym()) ;
                  println!( "  expected {}", exp_status ) ;
                  println!(
                    "       got {}", common::str_of_status(& status)
                  ) ;
                  println!("") ;
                }
              } else {
                panic!(
                  "no expected status for prop `{}`", prop.sym()
                )
              }
              map.remove( prop.sym() ) ;
            } else {
              panic!( "unknown prop `{}`", prop.sym() )
            }
          }
          if ! all_good {
            panic!("test failed")
          }
          if ! map.is_empty() {
            println!(
              "following properties were expected in test but not used:"
            ) ;
            for (sym, status) in map.into_iter() {
              println!("  {}: {}", sym, status)
            }
            panic!("test failed")
          }
        },
        Err( s ) => panic!(
          "could not analyze file `{}`:{}", file, s
        ),
      }
    }
  ) ;
}

/// Prints a `PropStatus` as test information.
pub fn str_of_status(status: & PropStatus) -> String {
  use kino::PropStatus::* ;
  match * status {
    Unknown => format!("<unknown>"),
    KTrue(ref n) => format!("<{}-true>", n),
    Falsified(ref cex) => format!("<{}-false>", cex.len()),
    Invariant(ref n) => format!("<{}-invariant>", n),
    MinInvariant(ref n, _) => format!("<{}-min-invariant>", n),
  }
}