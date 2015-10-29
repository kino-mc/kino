// Copyright 2015 Adrien Champion. See the COPYRIGHT file at the top-level
// directory of this distribution.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

/*! Basic traits and structures. */

pub use hcons::* ;

use std::sync::{ Arc, Mutex } ;

/** Under the hood an offset is a `u16`. */
#[derive(Debug,PartialEq,Eq,PartialOrd,Ord,Hash,Clone,Copy)]
pub struct Offset(u16) ;

impl Offset {
  /** Bytes to Offset conversion. */
  pub fn of_bytes(bytes: & [u8]) -> Offset {
    // -> Result<Offset, std::num::ParseIntError> {
    use std::str ;
    Offset(
      u16::from_str_radix( str::from_utf8(bytes).unwrap(), 10 ).unwrap()
    )
  }
  /** `usize` to Offset conversion. */
  pub fn of_int(int: usize) -> Offset {
    Offset(
      u16::from_str_radix( & int.to_string(), 10 ).unwrap()
    )
  }
}

/** One-state offset. */
pub struct Offset1(Offset) ;

/** Two-state offset. */
pub struct Offset2(Offset, Offset) ;



/** Redefinition of the thread-safe hash consign type. */
pub type HConsign<T> = Arc<Mutex<HashConsign<T>>> ;
