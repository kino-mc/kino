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
  format!("rsc/simple/{}.vmt", file)
}

#[test]
mk_test!{
  simple, path_to("simple"),
  "out_positive" => exp!(inv 1),
}

#[test]
mk_test!{
  simple_two_props, path_to("simple_two_props"),
  "out_positive" => exp!(inv 1),
  "out_le_10" => exp!(false 10),
}

#[test]
mk_test!{
  simple_false, path_to("simple_false"),
  "out_positive" => exp!(false 10),
  "out_positive1" => exp!(false 1),
}

#[test]
mk_test!{
  simple_init_cex, path_to("simple_init_cex"),
  "out_neg" => exp!(false 0),
}

#[test]
mk_test!{
  simple_rel, path_to("simple_rel"),
  "out_inc" => exp!(inv 1),
  "out_positive" => exp!(inv 1),
}

#[test]
mk_test!{
  simple_calls, path_to("simple_calls"),
  "out_le_10" => exp!(false 10),
  "out_positive" => exp!(inv 1),
}

#[test]
mk_test!{
  finite_state, path_to("finite_state"),
  "out_inc" => exp!(inv 4),
  "out_le_4" => exp!(inv 4),
}

#[test]
mk_test!{
  modular, path_to("modular"),
  "prop(b,1)" => exp!(false 1),
}

#[test]
mk_test!{
  modular_four, path_to("modular_four"),
  "prop(b,1)" => exp!(false 1),
  "prop(b,2)" => exp!(inv 1),
  "prop(b,3)" => exp!(inv 1),
  "prop(b,4)" => exp!(false 9),
}