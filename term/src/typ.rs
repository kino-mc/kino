// Copyright 2015 Adrien Champion. See the COPYRIGHT file at the top-level
// directory of this distribution.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

/*! Type representation and their values. */

use std::io ;
use base::{ Writable } ;

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

impl Writable for Type {
  #[inline(always)]
  fn write(& self, writer: & mut io::Write) -> io::Result<()> {
    write!(writer, "{}", self.to_str())
  }
}

/** Type used for boolean values. */
pub type Bool = bool ;

/** Type used for integer values. */
pub type Int = ::num::BigInt ;

/** Type used for rational values. */
pub type Rat = ::num::rational::BigRational ;