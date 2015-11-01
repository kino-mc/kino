/*! Type representation and their values. */

use std::io ;
use base::{ PrintSmt2, Offset2 } ;

/** A primitive type. */
#[derive(Clone,Debug,PartialEq,Eq,PartialOrd,Ord, Hash)]
pub enum Type {
  /** Bool type. */
  Bool,
  /** Int type. */
  Int,
  /** Rat type. */
  Rat
}

impl Type {
  /** String representation of a type. */
  #[inline(always)]
  pub fn to_str(& self) -> & 'static str {
    match * self {
      Type::Bool => "Bool",
      Type::Int => "Int",
      Type::Rat => "Real",
    }
  }
}

impl PrintSmt2 for Type {
  fn to_smt2(
    & self, writer: & mut io::Write, _: & Offset2
  ) -> io::Result<()> {
    write!(writer, "{}", self.to_str())
  }
}

/** Type used for boolean values. */
pub type Bool = bool ;

/** Type used for integer values. */
pub type Int = ::num::BigInt ;

/** Type used for rational values. */
pub type Rat = ::num::rational::BigRational ;