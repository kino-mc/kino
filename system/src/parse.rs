// Copyright 2015 Adrien Champion. See the COPYRIGHT file at the top-level
// directory of this distribution.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use nom::{ IResult, multispace } ;

use base::* ;
use term::{
  Sym, Term, Factory, ParseSts2
} ;


named!{
  pub sig_parser<Sig>,
  chain!(
    char!('(') ~
    opt!(multispace) ~
    args: separated_list!(
      opt!(multispace),
      Factory::parse_type
    ) ~
    opt!(multispace) ~
    char!(')'),
    || Sig::mk(args)
  )
}


pub fn sym_parser<'a>(
  bytes: & 'a [u8], f: & Factory
) -> IResult<'a, & 'a [u8], Sym> {
  f.parse_ident(bytes)
}


pub fn args_parser<'a>(
  bytes: & 'a [u8], f: & Factory
) -> IResult<'a, & 'a [u8], Args> {
  map!(
    bytes,
    separated_list!(
      opt!(multispace),
      delimited!(
        char!('('),
        chain!(
          sym: apply!(sym_parser, f) ~
          multispace ~
          typ: call!(Factory::parse_type),
          || (sym, typ)
        ),
        char!(')')
      )
    ),
    |args| Args::mk(args)
  )
}


pub fn state_parser<'a>(
  bytes: & 'a [u8], f: & Factory
) -> IResult<'a, & 'a [u8], State> {
  chain!(
    bytes,
    char!('(') ~
    opt!(multispace) ~
    tag!("define-state") ~
    multispace ~
    sym: apply!(sym_parser, f) ~
    opt!(multispace) ~
    args: apply!(args_parser, f) ~
    opt!(multispace) ~
    char!(')'),
    || State::mk(sym, args)
  )
}


pub fn fun_dec_parser<'a>(
  bytes: & 'a [u8], f: & Factory
) -> IResult<'a, & 'a [u8], FunDec> {
  chain!(
    bytes,
    char!('(') ~
    opt!(multispace) ~
    tag!("declare-fun") ~
    multispace ~
    sym: apply!(sym_parser, f) ~
    opt!(multispace) ~
    sig: sig_parser ~
    opt!(multispace) ~
    typ: call!(Factory::parse_type) ~
    opt!(multispace) ~
    char!(')'),
    || FunDec::mk(sym, sig, typ)
  )
}

pub fn term_parser<'a>(
  bytes: & 'a [u8], f: & Factory
) -> IResult<'a, & 'a [u8], Term> {
  f.parse_expr(bytes)
}

pub fn body_parser<'a>(
  bytes: & 'a [u8], f: & Factory
) -> IResult<'a, & 'a [u8], Body> {
  map!(
    bytes,
    apply!(term_parser, f),
    |term| Body::mk(term)
  )
}


pub fn fun_def_parser<'a>(
  bytes: & 'a [u8], f: & Factory
) -> IResult<'a, & 'a [u8], FunDef> {
  chain!(
    bytes,
    char!('(') ~
    opt!(multispace) ~
    tag!("define-fun") ~
    multispace ~
    sym: apply!(sym_parser, f) ~
    opt!(multispace) ~
    args: apply!(args_parser, f) ~
    opt!(multispace) ~
    typ: call!(Factory::parse_type) ~
    opt!(multispace) ~
    body: apply!(body_parser, f) ~
    opt!(multispace) ~
    char!(')'),
    || FunDef::mk(sym, args, typ, body)
  )
}


pub fn pred_parser<'a>(
  bytes: & 'a [u8], f: & Factory
) -> IResult<'a, & 'a [u8], Pred> {
  chain!(
    bytes,
    char!('(') ~
    opt!(multispace) ~
    tag!("define-pred") ~
    multispace ~
    sym: apply!(sym_parser, f) ~
    multispace ~
    state: apply!(sym_parser, f) ~
    opt!(multispace) ~
    body: apply!(body_parser, f) ~
    opt!(multispace) ~
    char!(')'),
    || Pred::mk(sym, state, body)
  )
}


pub fn init_def_parser<'a>(
  bytes: & 'a [u8], f: & Factory
) -> IResult<'a, & 'a [u8], Init> {
  chain!(
    bytes,
    char!('(') ~
    opt!(multispace) ~
    tag!("define-init") ~
    multispace ~
    sym: apply!(sym_parser, f) ~
    multispace ~
    state: apply!(sym_parser, f) ~
    opt!(multispace) ~
    body: apply!(body_parser, f) ~
    opt!(multispace) ~
    char!(')'),
    || Init::mk(sym, state, body)
  )
}


pub fn trans_def_parser<'a>(
  bytes: & 'a [u8], f: & Factory
) -> IResult<'a, & 'a [u8], Trans> {
  chain!(
    bytes,
    char!('(') ~
    opt!(multispace) ~
    tag!("define-trans") ~
    multispace ~
    sym: apply!(sym_parser, f) ~
    multispace ~
    state: apply!(sym_parser, f) ~
    opt!(multispace) ~
    body: apply!(body_parser, f) ~
    opt!(multispace) ~
    char!(')'),
    || Trans::mk(sym, state, body)
  )
}


pub fn sys_parser<'a>(
  bytes: & 'a [u8], f: & Factory
) -> IResult<'a, & 'a [u8], Sys> {
  chain!(
    bytes,
    char!('(') ~
    opt!(multispace) ~
    tag!("define-system") ~
    multispace ~
    sym: apply!(sym_parser, f) ~
    multispace ~
    state: apply!(sym_parser, f) ~
    multispace ~
    init: apply!(sym_parser, f) ~
    multispace ~
    trans: apply!(sym_parser, f) ~
    opt!(multispace) ~
    char!(')'),
    || Sys::mk(sym, state, init, trans)
  )
}