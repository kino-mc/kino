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
use std::fmt ;

use base::{ Writable } ;
use real_term::Cst ;

/** A primitive type. */
#[derive(Clone,Copy,Debug,PartialEq,Eq,PartialOrd,Ord,Hash)]
pub enum Type {
  /** Bool type. */
  Bool,
  /** Int type. */
  Int,
  /** Rat type. */
  Rat
}

impl fmt::Display for Type {
  fn fmt(& self, fmt: & mut fmt::Formatter) -> fmt::Result {
    write!(
      fmt, "{}",
      match * self {
        Type::Bool => "Bool",
        Type::Int => "Int",
        Type::Rat => "Real",
      }
    )
  }
}

impl Type {
  /// String representation of a type.
  #[inline]
  pub fn to_str(& self) -> & 'static str {
    match * self {
      Type::Bool => "Bool",
      Type::Int => "Int",
      Type::Rat => "Real",
    }
  }
  /// Default value of a type.
  #[inline]
  pub fn default(& self) -> Cst {
    match * self {
      Type::Bool => Cst::Bool(false),
      Type::Int => Cst::Int(
        Int::parse_bytes(b"0", 10).unwrap()
      ),
      Type::Rat => Cst::Rat(
        Rat::new(
          Int::parse_bytes(b"0", 10).unwrap(),
          Int::parse_bytes(b"1", 10).unwrap(),
        )
      ),
    }
  }
}

impl Writable for Type {
  #[inline]
  fn write(& self, writer: & mut io::Write) -> io::Result<()> {
    write!(writer, "{}", self.to_str())
  }
}

/** Type of boolean values. */
pub type Bool = bool ;

/** Type of integer values. */
pub type Int = ::num::BigInt ;

/** Type of rational values. */
pub type Rat = ::num::rational::BigRational ;