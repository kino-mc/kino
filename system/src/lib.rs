#![allow(non_upper_case_globals)]
// Copyright 2015 Adrien Champion. See the COPYRIGHT file at the top-level
// directory of this distribution.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

/*! Transition system library.

## Hash consing

[`Sym`][sym type] and [`Term`][term type] come from the kinō
[`term`][term crate] crate and are hash consed. Remember that one should
**never** create more that one [Factory][factory struct] for these. It is
thread-safe and can be cloned.
[`Context`][context struct] holds one for parsing.

## To do

* more clever input consumption in [`Context`][context struct]
* less copy in [`Context`][context struct]

[sym type]: ../term/type.Sym.html (Sym type)
[term type]: ../term/type.Term.html (Term type)
[term crate]: ../term/index.html (term crate)
[factory struct]: ../term/struct.Factory.html (Factory struct)
[context struct]: ctxt/struct.Context.html (Context struct)
*/


#[macro_use]
extern crate nom ;
extern crate term ;

mod base ;
// pub use base::{
//   Sig, Args, Uf, Fun, Prop, Sys
// } ;

mod parse ;

/** Reads and remembers what has been read. */
pub mod ctxt {
  pub use super::base::Callable ;
  pub use super::parse::{
    Res, Context
  } ;
  pub use super::parse::check::Error ;

}

mod sys ;
pub use sys::* ;
