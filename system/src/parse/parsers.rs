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
use super::{ Atom, Res } ;
use super::check::* ;
use term::{ Type, Sym, Factory, ParseVmt2 } ;
use term::parsing::* ;

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

/// Parses a repetition of multispace/comment.
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

mk_parser!{
  #[doc = "Type parser."]
  pub fn type_parser(bytes, offset: usize) -> Spnd<Type> {
    apply!(bytes, Factory::parse_type, offset)
  }
}
// named!{
//   type_parser<Type>,
//   call!(Factory::parse_type)
// }

/** Parses a signature. */
named!{
  sig_parser<Sig>,
  chain!(
    char!('(') ~
    opt!(space_comment) ~
    args: separated_list!(
      space_comment,
      map!( apply!(type_parser, 0), |t: Spnd<Type>| * t )
    ) ~
    opt!(space_comment) ~
    char!(')'),
    || Sig::mk(args)
  )
}

/** Parses a symbol. */
fn sym_parser<'a>(
  bytes: & 'a [u8], f: & Factory
) -> IResult<& 'a [u8], Sym> {
  f.parse_ident(bytes)
}

/** Parses some arguments. */
fn args_parser<'a>(
  bytes: & 'a [u8], f: & Factory
) -> IResult<& 'a [u8], Args> {
  chain!(
    bytes,
    char!('(') ~
    opt!(space_comment) ~
    args: separated_list!(
      space_comment,
      delimited!(
        char!('('),
        chain!(
          opt!(space_comment) ~
          sym: apply!(sym_parser, f) ~
          space_comment ~
          typ: map!( apply!(type_parser, 0), |t: Spnd<Type>| *t ) ~
          opt!(space_comment),
          || (sym, typ)
        ),
        char!(')')
      )
    ) ~
    opt!(space_comment) ~
    char!(')'),
    || Args::mk(args)
  )
}

/** Parses a function declaration. */
fn fun_dec_parser<'a>(
  bytes: & 'a [u8], c: & mut Context
) -> IResult<& 'a [u8], Result<(), Error>> {
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
    typ: map!( apply!(type_parser, 0), |t: Spnd<Type>| * t ) ~
    opt!(space_comment) ~
    char!(')'),
    || c.add_fun_dec(sym, sig, typ)
  )
}

/** Parses a term. */
fn term_parser<'a>(
  bytes: & 'a [u8], f: & Factory
) -> IResult<& 'a [u8], TermAndDep> {
  f.parse_expr(bytes)
}

/** Parses a function definition. */
fn fun_def_parser<'a>(
  bytes: & 'a [u8], c: & mut Context
) -> IResult<& 'a [u8], Result<(), Error>> {
  chain!(
    bytes,
    char!('(') ~
    opt!(space_comment) ~
    tag!("define-fun") ~
    space_comment ~
    sym: dbg_dmp!(apply!(sym_parser, c.factory())) ~
    opt!(space_comment) ~
    args: dbg_dmp!(apply!(args_parser, c.factory())) ~
    opt!(space_comment) ~
    typ: map!( apply!(type_parser, 0), |t: Spnd<Type>| * t ) ~
    opt!(space_comment) ~
    body: dbg_dmp!(apply!(term_parser, c.factory())) ~
    opt!(space_comment) ~
    char!(')'),
    || c.add_fun_def(sym, args, typ, body)
  )
}

/** Parses a state property definition. */
fn prop_parser<'a>(
  bytes: & 'a [u8], c: & mut Context
) -> IResult<& 'a [u8], Result<(), Error>> {
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
    || c.add_prop(sym, state, body)
  )
}

/** Parses a state relation definition. */
fn rel_parser<'a>(
  bytes: & 'a [u8], c: & mut Context
) -> IResult<& 'a [u8], Result<(), Error>> {
  chain!(
    bytes,
    char!('(') ~
    opt!(space_comment) ~
    tag!("define-rel") ~
    space_comment ~
    sym: apply!(sym_parser, c.factory()) ~
    space_comment ~
    state: apply!(sym_parser, c.factory()) ~
    opt!(space_comment) ~
    body: apply!(term_parser, c.factory()) ~
    opt!(space_comment) ~
    char!(')'),
    || c.add_rel(sym, state, body)
  )
}

fn sub_sys_parser<'a>(
  bytes: & 'a [u8], f: & Factory
) -> IResult<& 'a [u8], Vec<(Sym, Vec<TermAndDep>)>> {
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
fn _locals_parser<'a>(
  bytes: & 'a [u8], f: & Factory
) -> IResult<& 'a [u8], Vec<(Sym, Type, TermAndDep)>> {
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
            typ: map!( apply!(type_parser, 0), |t: Spnd<Type>| * t ) ~
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
fn sys_parser<'a>(
  bytes: & 'a [u8], c: & mut Context
) -> IResult<& 'a [u8], Result<(), Error>> {
  chain!(
    bytes,
    char!('(') ~
    opt!(space_comment) ~
    tag!("define-sys") ~
    space_comment ~
    sym: apply!(sym_parser, c.factory()) ~
    opt!(space_comment) ~
    state: apply!(args_parser, c.factory()) ~
    // opt!(space_comment) ~
    // locals: apply!(locals_parser, c.factory()) ~
    opt!(space_comment) ~
    init: apply!(term_parser, c.factory()) ~
    space_comment ~
    trans: apply!(term_parser, c.factory()) ~
    opt!(space_comment) ~
    sub_syss: apply!(sub_sys_parser, c.factory()) ~
    opt!(space_comment) ~
    char!(')'),
    || c.add_sys(sym, state, vec![], init, trans, sub_syss)
  )
}

/** Parses an item. */
pub fn item_parser<'a>(
  bytes: & 'a [u8], c: & mut Context
) -> IResult<& 'a [u8], Result<(), Error>> {
  preceded!(
    bytes,
    opt!(multispace),
    alt!(
      apply!(fun_dec_parser, c) |
      apply!(fun_def_parser, c) |
      apply!(prop_parser, c) |
      apply!(rel_parser, c) |
      apply!(sys_parser, c)
    )
  )
}

/** Parses a check. */
pub fn check_parser<'a>(
  bytes: & 'a [u8], c: & Context
) -> IResult<& 'a [u8], Result<Res, Error>> {
  chain!(
    bytes,
    opt!(space_comment) ~
    char!('(') ~
    opt!(space_comment) ~
    tag!("verify") ~
    space_comment ~
    sys: apply!(sym_parser, c.factory()) ~
    opt!(space_comment) ~
    props: delimited!(
      char!('('),
      delimited!(
        opt!(space_comment),
        separated_list!(
          space_comment,
          apply!(sym_parser, c.factory())
        ),
        opt!(space_comment)
      ),
      char!(')')
    ) ~
    opt!(space_comment) ~
    char!(')'),
    || check_check(c, sys, props, None)
  )
}

/** Parses an atom. */
pub fn atom_parser<'a>(
  bytes: & 'a [u8], f: & Factory
) -> IResult<& 'a [u8], Atom> {
  alt!(
    bytes,
    map!( apply!(sym_parser, f), |sym| Atom::Pos(sym) ) |
    delimited!(
      terminated!(char!('('), opt!(space_comment)),
      chain!(
        tag!("not") ~
        space_comment ~
        sym: apply!(sym_parser, f),
        || Atom::Neg(sym)
      ),
      preceded!(opt!(space_comment), char!(')'))
    )
  )
}

/** Parses a check with assumptions. */
pub fn check_assuming_parser<'a>(
  bytes: & 'a [u8], c: & Context
) -> IResult<& 'a [u8], Result<Res, Error>> {
  chain!(
    bytes,
    opt!(space_comment) ~
    char!('(') ~
    opt!(space_comment) ~
    tag!("verify-assuming") ~
    space_comment ~
    sys: apply!(sym_parser, c.factory()) ~
    opt!(space_comment) ~
    props: delimited!(
      char!('('),
      delimited!(
        opt!(space_comment),
        separated_list!(
          space_comment,
          apply!(sym_parser, c.factory())
        ),
        opt!(space_comment)
      ),
      char!(')')
    ) ~
    opt!(space_comment) ~
    atoms: delimited!(
      char!('('),
      delimited!(
        opt!(space_comment),
        separated_list!(
          space_comment,
          apply!(atom_parser, c.factory())
        ),
        opt!(space_comment)
      ),
      char!(')')
    ) ~
    opt!(space_comment) ~
    char!(')'),
    || check_check(c, sys, props, Some(atoms))
  )
}

/** Parses exit. */
named!{
  pub exit_parser< Result<Res, Error> >,
  preceded!(
    opt!(space_comment),
    delimited!(
      char!('('),
      delimited!(
        opt!(space_comment),
        map!( tag!("exit"), |_| Ok(Res::Exit) ),
        opt!(space_comment)
      ),
      char!(')')
    )
  )
}

/** Parses a check with assumptions. */
pub fn check_exit_parser<'a>(
  bytes: & 'a [u8], c: & Context
) -> IResult<& 'a [u8], Result<Res, Error>> {
  alt!(
    bytes,
    apply!(check_parser, c) |
    apply!(check_assuming_parser, c) |
    exit_parser
  )
}




