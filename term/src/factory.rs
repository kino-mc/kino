// Copyright 2015 Adrien Champion. See the COPYRIGHT file at the top-level
// directory of this distribution.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

/** Term factory stuff. */

use smt::ParseSmt2 ;

use ::sym::* ;
use ::term::* ;

struct Factory {
  sym: SymConsign,
  term: TermConsign,
}

// impl ParseSmt2 for Factory {
//   type Ident = id::Id ;
//   type Value = 
// }