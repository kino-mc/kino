// Copyright 2015 Adrien Champion. See the COPYRIGHT file at the top-level
// directory of this distribution.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

/*!

## TODO

* `num::rational` crash if denominator is zero. Can happen in parser. Parsing
only non-zero denominator will push the problem to function symbol application.
* `to_smt2` for terms copies way too much stuff

*/

extern crate num ;
#[macro_use]
extern crate nom ;
extern crate hashconsing as hcons ;
extern crate rsmt2 as smt ;

macro_rules! unimpl {
  () => ( panic!("not implemented") ) ;
}

mod base ;
pub use base::{
  State, PrintSmt2, Offset, Offset2, Smt2Offset
} ;
mod typ ;
pub use typ::{ Type, Bool, Int, Rat } ;
mod sym ;
pub use sym::{ Sym, SymMaker } ;
mod cst ;
pub use cst::{ Cst } ;
mod term ;
pub use term::{
  Term, VarMaker, CstMaker, OpMaker, BindMaker, AppMaker, UnTermOps
} ;
mod parser ;
mod factory ;
pub use factory::{ Factory } ;

/** Real, underlying representation of symbols, constants and terms. */
pub mod real {
  pub use sym::RealSym as Sym ;
  pub use cst::RealCst as Cst ;
  pub use term::RealTerm as Term ;
}