// Copyright 2015 Adrien Champion. See the COPYRIGHT file at the top-level
// directory of this distribution.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

/*! Term factory stuff. */

use nom::IResult ;

use smt::ParseSmt2 ;

use ::sym::* ;
use ::cst::* ;
use ::term::* ;

struct Factory {
  sym: SymConsign,
  term: TermConsign,
}

impl ParseSmt2 for Factory {
  type Ident = Sym ;
  type Value = Cst ;
  type Expr = Term ;
  type Proof = () ;
  fn parse_ident<'a>(
    & self, bytes: &'a [u8]
  ) -> IResult<'a, &'a [u8], Self::Ident> {
    panic!("not implemented")
  }
  fn parse_value<'a>(
    & self, bytes: &'a [u8]
  ) -> IResult<'a, &'a [u8], Self::Value> {
    panic!("not implemented")
  }
  fn parse_expr<'a>(
    & self, bytes: &'a [u8]
  ) -> IResult<'a, &'a [u8], Self::Expr> {
    panic!("not implemented")
  }
  fn parse_proof<'a>(
    & self, bytes: &'a [u8]
  ) -> IResult<'a, &'a [u8], Self::Proof> {
    panic!("not implemented")
  }
}