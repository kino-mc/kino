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
use super::Context ;
use super::check::* ;
use term::{ Type, Sym, TermAndDep, Factory, ParseSts2 } ;

/** Parses a multispace and a comment. */
named!{
  pub comment,
  chain!(
    opt!(multispace) ~
    char!(';') ~
    many0!(not_line_ending),
    || & []
  )
}

/** Parses a repetition of multispace/comment. */
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
  type_parser<Type>,
  call!(Factory::parse_type)
}

/** Parses a signature. */
named!{
  sig_parser<Sig>,
  chain!(
    char!('(') ~
    opt!(space_comment) ~
    args: separated_list!(
      opt!(space_comment),
      type_parser
    ) ~
    opt!(space_comment) ~
    char!(')'),
    || Sig::mk(args)
  )
}

/** Parses a symbol. */
fn sym_parser<'a>(
  bytes: & 'a [u8], f: & Factory
) -> IResult<'a, & 'a [u8], Sym> {
  f.parse_ident(bytes)
}

/** Parses some arguments. */
fn args_parser<'a>(
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
          typ: type_parser ~
          opt!(space_comment),
          || (sym, typ)
        ),
        char!(')')
      )
    ),
    |args| Args::mk(args)
  )
}

/** Parses a function declaration. */
fn fun_dec_parser<'a>(
  bytes: & 'a [u8], c: & mut Context
) -> IResult<'a, & 'a [u8], Result<(), Error>> {
  chain!(
    bytes,
    char!('(') ~
    opt!(space_comment) ~
    tag!("declare-fun") ~
    space_comment ~
    sym: apply!(sym_parser, c.factory()) ~
    opt!(space_comment) ~
    sig: sig_parser ~
    opt!(space_comment) ~
    typ: type_parser ~
    opt!(space_comment) ~
    char!(')'),
    || check_fun_dec(c, sym, sig, typ)
  )
}

/** Parses a term. */
fn term_parser<'a>(
  bytes: & 'a [u8], f: & Factory
) -> IResult<'a, & 'a [u8], TermAndDep> {
  f.parse_expr(bytes)
}

/** Parses a function definition. */
fn fun_def_parser<'a>(
  bytes: & 'a [u8], c: & mut Context
) -> IResult<'a, & 'a [u8], Result<(), Error>> {
  chain!(
    bytes,
    char!('(') ~
    opt!(space_comment) ~
    tag!("define-fun") ~
    space_comment ~
    sym: apply!(sym_parser, c.factory()) ~
    opt!(space_comment) ~
    args: apply!(args_parser, c.factory()) ~
    opt!(space_comment) ~
    typ: type_parser ~
    opt!(space_comment) ~
    body: apply!(term_parser, c.factory()) ~
    opt!(space_comment) ~
    char!(')'),
    || check_fun_def(c, sym, args, typ, body)
  )
}

/** Parses a property definition. */
fn prop_parser<'a>(
  bytes: & 'a [u8], c: & mut Context
) -> IResult<'a, & 'a [u8], Result<(), Error>> {
  chain!(
    bytes,
    char!('(') ~
    opt!(space_comment) ~
    tag!("define-prop") ~
    space_comment ~
    sym: apply!(sym_parser, c.factory()) ~
    space_comment ~
    state: apply!(sym_parser, c.factory()) ~
    opt!(space_comment) ~
    body: apply!(term_parser, c.factory()) ~
    opt!(space_comment) ~
    char!(')'),
    || check_prop(c, sym, state, body)
  )
}

fn sub_sys_parser<'a>(
  bytes: & 'a [u8], f: & Factory
) -> IResult<'a, & 'a [u8], Vec<(Sym, Vec<TermAndDep>)>> {
  delimited!(
    bytes,
    char!('('),
    many0!(
      chain!(
        opt!(space_comment) ~
        char!('(') ~
        opt!(space_comment) ~
        sym: apply!(sym_parser, f) ~
        params: many1!(
          preceded!(
            opt!(space_comment),
            apply!(term_parser, f)
          )
        ) ~
        opt!(space_comment) ~
        char!(')'),
        || (sym, params)
      )
    ),
    chain!( opt!(space_comment) ~ char!(')'), || () )
  )
}

/** Parses a local definitions. */
fn locals_parser<'a>(
  bytes: & 'a [u8], f: & Factory
) -> IResult<'a, & 'a [u8], Vec<(Sym, Type, TermAndDep)>> {
  delimited!(
    bytes,
    char!('('),
    many0!(
      preceded!(
        opt!(space_comment),
        delimited!(
          char!('('),
          chain!(
            opt!(space_comment) ~
            sym: apply!(sym_parser, f) ~
            space_comment ~
            typ: type_parser ~
            space_comment ~
            term: apply!(term_parser, f) ~
            opt!(space_comment),
            || (sym, typ, term)
          ),
          char!(')')
        )
      )
    ),
    preceded!(
      opt!(space_comment),
      char!(')')
    )
  )
}

/** Parses a system definition. */
fn new_sys_parser<'a>(
  bytes: & 'a [u8], c: & mut Context
) -> IResult<'a, & 'a [u8], Result<(), Error>> {
  chain!(
    bytes,
    char!('(') ~
    opt!(space_comment) ~
    tag!("define-system") ~
    space_comment ~
    sym: apply!(sym_parser, c.factory()) ~
    opt!(space_comment) ~
    char!('(') ~
    opt!(space_comment) ~
    state: apply!(args_parser, c.factory()) ~
    opt!(space_comment) ~
    char!(')') ~
    opt!(space_comment) ~
    locals: apply!(locals_parser, c.factory()) ~
    opt!(space_comment) ~
    init: apply!(term_parser, c.factory()) ~
    space_comment ~
    trans: apply!(term_parser, c.factory()) ~
    opt!(space_comment) ~
    sub_syss: apply!(sub_sys_parser, c.factory()) ~
    opt!(space_comment) ~
    char!(')'),
    || check_new_sys(c, sym, state, locals, init, trans, sub_syss)
  )
}

/** Parses an item. */
pub fn item_parser<'a>(
  bytes: & 'a [u8], c: & mut Context
) -> IResult<'a, & 'a [u8], Result<(), Error>> {
  preceded!(
    bytes,
    opt!(multispace),
    alt!(
      apply!(fun_dec_parser, c) |
      apply!(fun_def_parser, c) |
      apply!(prop_parser, c) |
      apply!(new_sys_parser, c)
    )
  )
}

/** Parses a check. */
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

/** Parses exit. */
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