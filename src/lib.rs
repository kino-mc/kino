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

#[macro_use]
extern crate error_chain ;
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

// use term::{ Sym, SymMaker } ;
use system::Prop ;
pub use system::Error as SysError ;
// pub use unroll::* ;
// pub use common::* ;

/// Top level errors.
pub mod errors {
  use SysError ;
  error_chain!{
    types {
      Error, ErrorKind, ResExt, Res ;
    }
    errors {
      #[doc = "Error during system creation."]
      SysError(e: SysError) {
        description("error in system creation")
        display("system error: {}", e)
      }
      #[doc = "Error during an analysis."]
      AnalysisError(s: String) {
        description("error during analysis")
        display("{}", s)
      }
    }
  }
}
use errors::* ;

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
pub fn load(path: & str) -> Res< (Context, CtxtRes) > {
  use std::fs::File ;
  use term::Factory ;
  match File::open(path) {
    Ok(mut file) => {
      let factory = Factory::mk() ;
      let mut context = Context::mk(factory, 1000) ;
      match context.read(& mut file) {
        Ok(res) => Ok( (context, res) ),
        Err(e) => bail!( ErrorKind::SysError(e) ),
      }
    },
    Err(e) => bail!(
      ErrorKind::SysError( SysError::Io(e) )
    ),
  }
}

/// Loads a file, creates a context, runs the master.
pub fn analyze(path: & str) -> Res<(Context, Vec<Prop>)> {
  let (mut context, res) = try!( load(path) ) ;
  match res {
    CtxtRes::Success => Err("got success".into()),
    CtxtRes::Exit => Ok( (context, vec![]) ),
    CtxtRes::Check(sys, props) => {
      let log = ::common::log::MasterLog::default() ;
      let conf = ::common::conf::Master::default() ;
      match Master::launch(
        & log, & mut context, sys, props.clone(), None, conf
      ) {
        Ok(()) => Ok( (context, props) ),
        Err(()) => Err(
          "master did not return successfully".into()
        ),
      }
    },
    CtxtRes::CheckAss(_, _, _) => Err(
      "verify assuming is not supported".into()
    ),
  }
}