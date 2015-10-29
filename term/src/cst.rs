// Copyright 2015 Adrien Champion. See the COPYRIGHT file at the top-level
// directory of this distribution.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

/** Constant structures. */

use ::base::* ;
use ::typ ;

use self::Constant::* ;

#[derive(Debug,Clone,PartialEq,Eq,PartialOrd,Ord,Hash)]
pub enum Constant {
  Bool(typ::Bool),
  Int(typ::Int),
  Rat(typ::Rat),
}

pub type Cst = HConsed<Constant> ;
pub type CstConsign = HConsign<Constant> ;

pub trait CstMaker<Const> {
  fn cst(& self, Const) -> Cst ;
}
impl<
  'a, Const: Clone, T: Sized + CstMaker<Const>
> CstMaker<& 'a Const> for T {
  fn cst(& self, cst: & 'a Const) -> Cst {
    (self as & CstMaker<Const>).cst(cst.clone())
  }
}
impl CstMaker<typ::Bool> for CstConsign {
  fn cst(& self, b: typ::Bool) -> Cst {
    self.lock().unwrap().mk( Bool(b) )
  }
}
impl CstMaker<typ::Int> for CstConsign {
  fn cst(& self, i: typ::Int) -> Cst {
    self.lock().unwrap().mk( Int(i) )
  }
}
impl CstMaker<typ::Rat> for CstConsign {
  fn cst(& self, r: typ::Rat) -> Cst {
    self.lock().unwrap().mk( Rat(r) )
  }
}
