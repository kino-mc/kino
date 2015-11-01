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

use base::{ Writable, HConsed, HConsign } ;


/** Underlying representation of function symbols. */
#[derive(Debug,PartialEq,Eq,PartialOrd,Ord,Hash)]
pub struct RealSym {
  /** The `String` representing the function symbol. */
  sym: String
}

/** Hash consed function symbol. */
pub type Sym = HConsed<RealSym> ;

impl Writable for Sym {
  #[inline(always)]
  fn write(& self, writer: & mut io::Write) -> io::Result<()> {
    write!(writer, "{}", self.get().sym)
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