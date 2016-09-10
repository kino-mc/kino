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

//! API for the kinō model-checker.

extern crate term ;
extern crate system ;
extern crate unroll ;
#[macro_use]
extern crate common ;
extern crate bmc ;
extern crate kind ;
extern crate twind ;
extern crate tig ;
extern crate pruner ;

mod master ;

pub use term::* ;
pub use system::* ;
pub use unroll::* ;
pub use common::* ;

/// The techniques provided by kino.
pub mod teks {
  pub use bmc::Bmc ;
  pub use kind::KInd ;
  pub use tig::* ;
}

pub use master::Master ;
pub use system::ctxt::Context ;
use system::ctxt::Res as CtxtRes ;

/// Loads a file, creates a context.
pub fn load(path: & str) -> Result< (Context, CtxtRes), String> {
  use std::fs::File ;
  use term::Factory ;
  match File::open(path) {
    Ok(mut file) => {
      let factory = Factory::mk() ;
      let mut context = Context::mk(factory, 1000) ;
      match context.read(& mut file) {
        Ok(res) => Ok( (context, res) ),
        Err(e) => Err(
          format!("error reading file `{}`\n{}", path, e)
        ),
      }
    },
    Err(e) => Err(
      format!("could not open file `{}`\n{}", path, e)
    ),
  }
}

/// Loads a file, creates a context, runs the master.
pub fn analyze(path: & str) -> Result< (Context, Vec<Prop>), String> {
  let (mut context, res) = try!( load(path) ) ;
  match res {
    CtxtRes::Exit => Ok( (context, vec![]) ),
    CtxtRes::Check(sys, props) => {
      let log = ::common::log::MasterLog::default() ;
      let conf = ::common::conf::Master::default() ;
      match Master::launch(
        & log, & mut context, sys, props.clone(), None, conf
      ) {
        Ok(()) => Ok( (context, props) ),
        Err(()) => Err(
          format!("master did not return successfully")
        ),
      }
    },
    CtxtRes::CheckAss(_, _, _) => Err(
      format!("verify assuming is not supported")
    ),
  }
}