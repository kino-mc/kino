// Copyright 2015 Adrien Champion. See the COPYRIGHT file at the top-level
// directory of this distribution.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

/*! Function symbols. */

use std::io ;
use std::fmt ;

use base::{ SymPrintStyle, SymWritable, HConsed, HConsign } ;


/** Underlying representation of function symbols. */
#[derive(Clone,Debug,PartialEq,Eq,PartialOrd,Ord,Hash)]
pub struct RealSym {
  /** The `String` representing the function symbol. */
  sym: String
}
impl RealSym {
  pub fn sym(& self) -> & str { & self.sym }
}

impl fmt::Display for RealSym {
  fn fmt(& self, fmt: & mut fmt::Formatter) -> fmt::Result {
    write!(fmt, "|{}|", self.sym)
  }
}

/** Hash consed function symbol. */
pub type Sym = HConsed<RealSym> ;

impl SymWritable for RealSym {
  #[inline(always)]
  fn write(
    & self, writer: & mut io::Write, style: SymPrintStyle
  ) -> io::Result<()> {
    use base::SymPrintStyle::* ;
    match style {
      Internal => write!(writer, " {}", self.sym),
      External => write!(writer, "{}", self.sym),
    }
  }
}

impl SymWritable for Sym {
  #[inline(always)]
  fn write(
    & self, writer: & mut io::Write, style: SymPrintStyle
  ) -> io::Result<()> {
    self.get().write(writer, style)
  }
}

/** Hash cons table for function symbols. */
pub type SymConsign = HConsign<RealSym> ;

/** Can create a function symbol. */
pub trait SymMaker<T> {
  /** Creates a function symbol. */
  #[inline(always)]
  fn sym(& self, T) -> Sym ;
}

impl SymMaker<String> for SymConsign {
  fn sym(& self, sym: String) -> Sym {
    self.lock().unwrap().mk( RealSym { sym: sym } )
  }
}
impl<'a> SymMaker<& 'a str> for SymConsign {
  fn sym(& self, sym: & 'a str) -> Sym {
    self.lock().unwrap().mk( RealSym { sym: sym.to_string() } )
  }
}