// Copyright 2016 Adrien Champion. See the COPYRIGHT file at the top-level
// directory of this distribution.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

extern crate kino_api as kino ;

#[macro_use]
mod common ;

/// Returns the complete path to a file (given *without* the `.vmt`
/// extension).
fn path_to(file: & str) -> String {
  format!("rsc/from_kind/{}.vmt", file)
}

#[test]
mk_test!{
  counters, path_to("counters"),
  "top_prop_1" => exp!(inv 7),
  "top_prop_2" => exp!(inv 2),
  "top_prop_3" => exp!(inv 2),
}

