/*! Type-related structures and parsers. */

#[derive(Clone,Debug,PartialEq,Eq,PartialOrd,Ord, Hash)]
pub enum Type {
  Bool, Int, Rat
}

impl Type {
  pub fn to_str(& self) -> & 'static str {
    match * self {
      Type::Bool => "Bool",
      Type::Int => "Int",
      Type::Rat => "Real",
    }
  }
}

pub type Bool = bool ;

pub type Int = ::num::BigInt ;

pub type Rat = ::num::rational::BigRational ;