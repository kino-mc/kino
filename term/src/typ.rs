/*! Type-related structures and parsers. */

#[derive(Clone,Debug,PartialEq,Eq,PartialOrd,Ord, Hash)]
pub enum Type {
  Bool, Int, Rat
}

pub type Bool = bool ;

pub type Int = ::num::BigInt ;

pub type Rat = ::num::rational::BigRational ;

named!{ pub typ_parser<Type>,
  alt!(
    map!( tag!("Bool"), |_| Type::Bool ) |
    map!( tag!("Int"),  |_| Type::Int  ) |
    map!( tag!("Rat"),  |_| Type::Rat  )
  )
}