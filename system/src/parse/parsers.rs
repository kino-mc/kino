// Copyright 2015 Adrien Champion. See the COPYRIGHT file at the top-level
// directory of this distribution.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use nom::{ IResult, multispace, not_line_ending } ;

use base::* ;
use parse::* ;
use term::{
  Sym, StsResult, Factory, ParseSts2
} ;

named!{
  pub comment,
  chain!(
    opt!(multispace) ~
    char!(';') ~
    many0!(not_line_ending),
    || & []
  )
}

named!{
  space_comment<()>,
  map!(
    many0!(
      alt!(
        comment | multispace
      )
    ),
    |_| ()
  )
}


named!{
  pub sig_parser<Sig>,
  chain!(
    char!('(') ~
    opt!(space_comment) ~
    args: separated_list!(
      opt!(space_comment),
      Factory::parse_type
    ) ~
    opt!(space_comment) ~
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
      opt!(space_comment),
      delimited!(
        char!('('),
        chain!(
          opt!(space_comment) ~
          sym: apply!(sym_parser, f) ~
          space_comment ~
          typ: call!(Factory::parse_type) ~
          opt!(space_comment),
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
    opt!(space_comment) ~
    tag!("define-state") ~
    space_comment ~
    sym: apply!(sym_parser, f) ~
    opt!(space_comment) ~
    args: apply!(args_parser, f) ~
    opt!(space_comment) ~
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
    opt!(space_comment) ~
    tag!("declare-fun") ~
    space_comment ~
    sym: apply!(sym_parser, f) ~
    opt!(space_comment) ~
    sig: sig_parser ~
    opt!(space_comment) ~
    typ: call!(Factory::parse_type) ~
    opt!(space_comment) ~
    char!(')'),
    || FunDec::mk(sym, sig, typ)
  )
}

pub fn term_parser<'a>(
  bytes: & 'a [u8], f: & Factory
) -> IResult<'a, & 'a [u8], StsResult> {
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
    opt!(space_comment) ~
    tag!("define-fun") ~
    space_comment ~
    sym: apply!(sym_parser, f) ~
    opt!(space_comment) ~
    args: apply!(args_parser, f) ~
    opt!(space_comment) ~
    typ: call!(Factory::parse_type) ~
    opt!(space_comment) ~
    body: apply!(body_parser, f) ~
    opt!(space_comment) ~
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
    opt!(space_comment) ~
    tag!("define-pred") ~
    space_comment ~
    sym: apply!(sym_parser, f) ~
    space_comment ~
    state: apply!(sym_parser, f) ~
    opt!(space_comment) ~
    body: apply!(body_parser, f) ~
    opt!(space_comment) ~
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
    opt!(space_comment) ~
    tag!("define-init") ~
    space_comment ~
    sym: apply!(sym_parser, f) ~
    space_comment ~
    state: apply!(sym_parser, f) ~
    opt!(space_comment) ~
    body: apply!(body_parser, f) ~
    opt!(space_comment) ~
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
    opt!(space_comment) ~
    tag!("define-trans") ~
    space_comment ~
    sym: apply!(sym_parser, f) ~
    space_comment ~
    state: apply!(sym_parser, f) ~
    opt!(space_comment) ~
    body: apply!(body_parser, f) ~
    opt!(space_comment) ~
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
    opt!(space_comment) ~
    tag!("define-system") ~
    space_comment ~
    sym: apply!(sym_parser, f) ~
    space_comment ~
    state: apply!(sym_parser, f) ~
    space_comment ~
    init: apply!(sym_parser, f) ~
    space_comment ~
    trans: apply!(sym_parser, f) ~
    opt!(space_comment) ~
    char!(')'),
    || Sys::mk(sym, state, init, trans)
  )
}

pub fn item_parser<'a>(
  bytes: & 'a [u8], c: & mut Context
) -> IResult<'a, & 'a [u8], Result<(), Error>> {
  use base::Item::* ;
  map!(
    bytes,
    preceded!(
      opt!(multispace),
      alt!(
        map!( apply!(state_parser, c.factory()), |out| St(out) ) |
        map!( apply!(fun_dec_parser, c.factory()), |out| FDc(out) ) |
        map!( apply!(fun_def_parser, c.factory()), |out| FDf(out) ) |
        map!( apply!(pred_parser, c.factory()), |out| P(out) ) |
        map!( apply!(init_def_parser, c.factory()), |out| I(out) ) |
        map!( apply!(trans_def_parser, c.factory()), |out| T(out) ) |
        map!( apply!(sys_parser, c.factory()), |out| S(out) )
      )
    ),
    |item| c.add(item)
  )
}



pub fn check_parser<'a>(
  bytes: & 'a [u8], f: & Factory
) -> IResult<'a, & 'a [u8], (Sym,Vec<Sym>)> {
  chain!(
    bytes,
    opt!(space_comment) ~
    char!('(') ~
    opt!(space_comment) ~
    tag!("check") ~
    space_comment ~
    sys: apply!(sym_parser, f) ~
    opt!(space_comment) ~
    props: delimited!(
      char!('('),
      delimited!(
        opt!(space_comment),
        separated_list!(
          space_comment,
          apply!(sym_parser, f)
        ),
        opt!(space_comment)
      ),
      char!(')')
    ) ~
    opt!(space_comment) ~
    char!(')'),
    || (sys, props)
  )
}

named!{
  pub exit_parser,
  preceded!(
    opt!(space_comment),
    delimited!(
      char!('('),
      delimited!(
        opt!(space_comment),
        tag!("exit"),
        opt!(space_comment)
      ),
      char!(')')
    )
  )
}