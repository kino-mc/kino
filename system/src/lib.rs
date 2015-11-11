#![allow(non_upper_case_globals)]
#![deny(missing_docs)]
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

use std::sync::Arc ;

mod base ;

mod parse ;

/** Real types of the elements of a context. */
pub mod real {
  pub use base::{
    Sig, Args, Uf, Fun, Prop, Sys, Callable
  } ;
}

/** Reads and remembers what has been read. */
pub mod ctxt {
  pub use super::base::Callable ;
  pub use super::parse::{
    Res, Context
  } ;
  pub use super::parse::check::Error ;
}

pub use base::{ CallSet, PropSet } ;

/** A signature, a list of types. Used only in `Uf`. */
pub type Sig = Arc<base::Sig> ;
/** A list of typed formal parameters. */
pub type Args = Arc<base::Args> ;
/** An uninterpreted function. */
pub type Uf = Arc<base::Uf> ;
/** A function (actually a macro in SMT-LIB). */
pub type Fun = Arc<base::Fun> ;
/** Wraps an (uninterpreted) function. */
pub type Callable = Arc<base::Callable> ;
/** A property. */
pub type Prop = Arc<base::Prop> ;
/** A transition system. */
pub type Sys = Arc<base::Sys> ;


