// Copyright 2015 Adrien Champion. See the COPYRIGHT file at the top-level
// directory of this distribution.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

#![allow(non_upper_case_globals)]
#![deny(missing_docs)]

/*! API for the kinō model-checker. */

extern crate term ;
extern crate system ;
extern crate unroll ;
extern crate common ;
extern crate bmc ;
extern crate kind ;
extern crate tig as inv_gen ;

mod master ;

pub use term::* ;
pub use system::* ;
pub use unroll::* ;
pub use common::* ;

/** The techniques provided by kino. */
pub mod teks {
  pub use bmc::Bmc ;
  pub use kind::KInd ;
  pub use inv_gen::* ;
}

pub use master::Master ;
pub use system::ctxt::Context ;