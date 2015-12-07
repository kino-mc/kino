// Copyright 2015 Adrien Champion. See the COPYRIGHT file at the top-level
// directory of this distribution.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

#![deny(missing_docs)]

/*! Handles all the configuration aspects of kino, including CLAP. */

extern crate common ;
extern crate bmc ;
extern crate kind ;

pub use bmc::BmcConf ;
pub use kind::KIndConf ;

/** Master kino configuration. */
pub struct KinoConf {
  _nothing_yet: ()
}
impl KinoConf {
  /** Default kino master configuration. */
  pub fn default() -> Self {
    KinoConf { _nothing_yet: () }
  }
}

/** Global configuration for master + techniques. */
pub struct Conf {
  master: KinoConf,
  bmc: Option<BmcConf>,
  kind: Option<KIndConf>,
}
impl Conf {
  /** Default configuration. */
  pub fn default() -> Self {
    Conf {
      master: KinoConf::default(),
      bmc: Some( BmcConf::default() ),
      kind: Some( KIndConf::default() ),
    }
  }

  /** Master configuration. */
  pub fn master(& self) -> & KinoConf {
    & self.master
  }
  /** BMC configuration. */
  pub fn bmc(& self) -> & Option<BmcConf> {
    & self.bmc
  }
  /** K-induction configuration. */
  pub fn kind(& self) -> & Option<KIndConf> {
    & self.kind
  }
}
