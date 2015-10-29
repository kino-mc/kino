// Copyright 2015 Adrien Champion. See the COPYRIGHT file at the top-level
// directory of this distribution.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

/** Identifiers structures and parsers. */

use ::base::* ;
use ::sym::* ;

#[derive(PartialEq,Eq,PartialOrd,Ord,Hash)]
pub struct Identifier {
  sym: String
}

pub type Id = HConsed<Identifier> ;

pub type IdConsign = HConsign<Identifier> ;

pub trait IdFactory {
  fn of_str(& self, & str) -> Id ;
  fn of_string(& self, String) -> Id ;
}

impl IdFactory for IdConsign {
  fn of_str(& self, sym: & str) -> Id {
    self.lock().unwrap().mk( Identifier { sym: sym.to_string() } )
  }
  fn of_string(& self, sym: String) -> Id {
    self.lock().unwrap().mk( Identifier { sym: sym } )
  }
}