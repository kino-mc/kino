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

/*! Main project for kinō.

## To do:

write stuff here
*/

extern crate nom ;
extern crate term ;
extern crate system ;
extern crate common ;
extern crate bmc ;
extern crate kind ;

use std::process::exit ;

use system::ctxt::* ;

use common::Tek::Kino ;
use common::log::{ MasterLog, Formatter, Styler } ;

pub mod master ;

use master::Master ;

fn main() {
  use std::fs::File ;

  let log = MasterLog::default() ;

  log.sep() ;
  log.sep() ;

  let (conf, file) = match common::conf::Master::mk(& log) {
    Ok(conf) => conf,
    Err(e) => {
      log.title("CLA parsing") ;
      log.nl() ;
      log.bad(& Kino, & e) ;
      log.trail() ;
      log.sep() ;
      log.sep() ;
      exit(2)
    },
  } ;

  for file in vec![file] {
    let factory = term::Factory::mk() ;
    let mut context = Context::mk(factory, 10000) ;

    log.title( & format!("opening \"{}\"", file) ) ;
    match File::open(& file) {
      Ok(mut f) => {
        log.print( & log.mk_happy("success") ) ;
        log.title("parsing") ;
        match context.read(& mut f) {
          Ok(res) => {
            log.print( & log.mk_happy("success") ) ;

            log.title("Context") ;
            for line in context.lines().lines() {
              log.print(line)
            } ;

            log.title("Query") ;
            for line in res.lines().lines() {
              log.print(line)
            } ;

            match res {
              Res::Exit => (),
              Res::Check(sys, props) => {
                log.trail() ;
                let _ = Master::launch(& log, & context, sys, props, None) ;
              },
              Res::CheckAss(_, _, _) => {
                log.bad(
                  & Kino, "verify with assumption is not supported"
                ) ;
                log.trail()
              },
            }
          },
          Err( e ) => {
            log.nl() ;
            log.bad( & Kino, & format!("{}", e) ) ;
            log.trail()
          },
        }
      },
      Err(e) => {
        log.nl() ;
        log.bad( & Kino, & format!("{}", e) ) ;
        log.trail()
      },
    } ;

    log.sep()
  }
  ()
}
