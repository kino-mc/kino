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

`num::rational` crash if denominator is zero. Can happen in parser. Parsing
only non-zero denominator will push the problem to function symbol application.

*/

extern crate num ;
#[macro_use]
extern crate nom ;
extern crate hashconsing as hcons ;
extern crate rsmt2 as smt ;

mod base ;
pub mod typ ;
pub mod sym ;
// pub mod id ;
pub mod cst ;
pub mod term ;
pub mod parser ;
pub mod factory ;

pub use base::* ;
