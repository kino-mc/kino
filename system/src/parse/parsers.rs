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
use super::Context ;
use super::{ Atom, Res } ;
use super::check::* ;
use term::{ Type, Sym, Factory } ;
use term::parsing::* ;
use term::parsing::vmt::* ;

mk_parser!{
  #[doc = "/// Parses a signature."]
  pub fn sig_parser(bytes, offset: usize) -> Spnd<Sig> {
    let mut len = 0 ;
    do_parse!(
      bytes,
      len_set!(len < char '(') >>
      len_add!(len < opt spc cmt) >>
      args: separated_list!(
        len_add!(len < spc cmt),
        map!(
          apply!(type_parser, 0), |t: Spnd<Type>| {
            len += t.len() ;
            t
          }
        )
      ) >>
      len_add!(len < opt spc cmt) >>
      len_add!(len < char ')') >> (
        Spnd::len_mk(Sig::mk(args), offset, len)
      )
    )
  }
}

/// Parses some arguments.
fn args_parser<'a>(
  bytes: & 'a [u8], offset: usize, f: & Factory
) -> IResult<& 'a [u8], Spnd<Args>> {
  let mut len = 0 ;
  do_parse!(
    bytes,
    len_set!(len < char '(') >>
    len_add!(len < opt spc cmt) >>
    args: separated_list!(
      len_add!(len < spc cmt),
      delimited!(
        len_add!(len < char '('),
        do_parse!(
          len_add!(len < opt spc cmt) >>
          sym: len_add!(
            len < spn thru apply!(sym_parser, 0, f)
          ) >>
          len_add!(len < spc cmt) >>
          typ: len_add!(
            len < spn thru apply!(type_parser, 0)
          ) >>
          len_add!(len < opt spc cmt) >> (
            (sym, typ)
          )
        ),
        len_add!(len < char ')')
      )
    ) >>
    len_add!(len < opt spc cmt) >>
    len_add!(len < char ')') >> (
      Spnd::len_mk(Args::mk(args), offset, len)
    )
  )
}

/// Parses a function declaration.
fn fun_dec_parser<'a>(
  bytes: & 'a [u8], offset: usize, c: & mut Context
) -> IResult<& 'a [u8], Result<usize, Error>> {
  let mut len = 0 ;
  do_parse!(
    bytes,
    len_set!(len < char '(') >>
    len_add!(len < opt spc cmt) >>
    len_add!(len < bytes tag!("declare-fun")) >>
    len_add!(len < spc cmt) >>
    sym: len_add!(
      len < spn thru apply!(sym_parser, offset + len, c.factory())
    ) >>
    len_add!(len < opt spc cmt) >>
    sig: len_add!(
      len < spn apply!(sig_parser, 0)
    ) >>
    len_add!(len < opt spc cmt) >>
    typ: len_add!(
      len < spn thru apply!(type_parser, 0)
    ) >>
    len_add!(len < opt spc cmt) >>
    len_add!(len < char ')') >> (
      c.add_fun_dec(sym, sig, typ).map(|()| len)
    )
  )
}

/// Parses a function definition.
fn fun_def_parser<'a>(
  bytes: & 'a [u8], offset: usize, c: & mut Context
) -> IResult<& 'a [u8], Result<usize, Error>> {
  let mut len = 0 ;
  do_parse!(
    bytes,
    len_set!(len < char '(') >>
    len_add!(len < opt spc cmt) >>
    len_add!(len < bytes tag!("define-fun")) >>
    len_add!(len < spc cmt) >>
    sym: len_add!(
      len < spn thru apply!(sym_parser, offset + len, c.factory())
    ) >>
    len_add!(len < opt spc cmt) >>
    args: len_add!(
      len < spn apply!(args_parser, offset + len, c.factory())
    ) >>
    len_add!(len < opt spc cmt) >>
    typ: len_add!(
      len < spn thru apply!(type_parser, offset + len)
    ) >>
    len_add!(len < opt spc cmt) >>
    body: len_add!(
      len < trm apply!(term_parser, offset + len, c.factory())
    ) >>
    len_add!(len < opt spc cmt) >>
    len_add!(len < char ')') >> (
      c.add_fun_def(sym, args, typ, body).map(|()| len)
    )
  )
}

/// Parses a state property definition.
fn prop_parser<'a>(
  bytes: & 'a [u8], offset: usize, c: & mut Context
) -> IResult<& 'a [u8], Result<usize, Error>> {
  let mut len = 0 ;
  do_parse!(
    bytes,
    len_set!(len < char '(') >>
    len_add!(len < opt spc cmt) >>
    len_add!(len < bytes tag!("define-prop")) >>
    len_add!(len < spc cmt) >>
    sym: len_add!(
      len < spn thru apply!(sym_parser, offset + len, c.factory())
    ) >>
    len_add!(len < spc cmt) >>
    sys: len_add!(
      len < spn thru apply!(sym_parser, offset + len, c.factory())
    ) >>
    len_add!(len < opt spc cmt) >>
    body: len_add!(
      len < trm apply!(term_parser, offset + len, c.factory())
    ) >>
    len_add!(len < opt spc cmt) >>
    len_add!(len < char ')') >> (
      c.add_prop(sym, sys, body).map(|()| len)
    )
  )
}

/// Parses a state relation definition.
fn rel_parser<'a>(
  bytes: & 'a [u8], offset: usize, c: & mut Context
) -> IResult<& 'a [u8], Result<usize, Error>> {
  let mut len = 0 ;
  do_parse!(
    bytes,
    len_set!(len < char '(') >>
    len_add!(len < opt spc cmt) >>
    len_add!(len < bytes tag!("define-rel")) >>
    len_add!(len < spc cmt) >>
    sym: len_add!(
      len < spn thru apply!(sym_parser, offset + len, c.factory())
    ) >>
    len_add!(len < spc cmt) >>
    sys: len_add!(
      len < spn thru apply!(sym_parser, offset + len, c.factory())
    ) >>
    len_add!(len < opt spc cmt) >>
    body: len_add!(
      len < trm apply!(term_parser, offset + len, c.factory())
    ) >>
    len_add!(len < opt spc cmt) >>
    len_add!(len < char ')') >> (
      c.add_rel(sym, sys, body).map(|()| len)
    )
  )
}

fn sub_sys_parser<'a>(
  bytes: & 'a [u8], offset: usize, f: & Factory
) -> IResult<& 'a [u8], (usize, Vec<(Spnd<Sym>, Vec<TermAndDep>)>)> {
  let mut len = 0 ;
  map!(
    bytes,
    delimited!(
      len_set!(len < char '('),
      many0!(
        do_parse!(
          len_add!(len < opt spc cmt) >>
          len_add!(len < char '(') >>
          len_add!(len < opt spc cmt) >>
          sym: len_add!(
            len < spn thru apply!(sym_parser, offset + len, f)
          ) >>
          params: many1!(
            preceded!(
              len_add!(len < opt spc cmt),
              len_add!(
                len < trm apply!(term_parser, 0, f)
              )
            )
          ) >>
          len_add!(len < opt spc cmt) >>
          len_add!(len < char ')') >> (
            (sym, params)
          )
        )
      ),
      do_parse!(
        len_add!(len < opt spc cmt) >>
        len_add!(len < char ')') >> ( () )
      )
    ),
    |vec| (len, vec)
  )
}

// /// Parses local definitions.
// fn _locals_parser<'a>(
//   bytes: & 'a [u8], f: & Factory
// ) -> IResult<& 'a [u8], Vec<(Sym, Type, TermAndDep)>> {
//   delimited!(
//     bytes,
//     char!('('),
//     many0!(
//       preceded!(
//         opt!(space_comment),
//         delimited!(
//           char!('('),
//           do_parse!(
//             opt!(space_comment) >>
//             sym: apply!(sym_parser_2, f) >>
//             space_comment >>
//             typ: map!( apply!(type_parser, 0), |t: Spnd<Type>| * t ) >>
//             space_comment >>
//             term: apply!(term_parser, 0, f) >>
//             opt!(space_comment) >> (
//               (sym, typ, term)
//             )
//           ),
//           char!(')')
//         )
//       )
//     ),
//     preceded!(
//       opt!(space_comment),
//       char!(')')
//     )
//   )
// }

/// Parses a system definition.
fn sys_parser<'a>(
  bytes: & 'a [u8], offset: usize, c: & mut Context
) -> IResult<& 'a [u8], Result<usize, Error>> {
  let mut len = 0 ;
  do_parse!(
    bytes,
    len_set!(len < char '(') >>
    len_add!(len < opt spc cmt) >>
    len_add!(len < bytes tag!("define-sys") ) >>
    len_add!(len < spc cmt) >>
    sym: len_add!(
      len < spn apply!(sym_parser, offset + len, c.factory())
    ) >>
    len_add!(len < opt spc cmt) >>
    state: len_add!(
      len < spn apply!(args_parser, offset + len, c.factory())
    ) >>
    // opt!(space_comment) >>
    // locals: apply!(locals_parser, c.factory()) >>
    len_add!(len < opt spc cmt) >>
    init: len_add!(
      len < trm apply!(term_parser, offset + len, c.factory())
    ) >>
    len_add!(len < spc cmt) >>
    trans: len_add!(
      len < trm apply!(term_parser, offset + len, c.factory())
    ) >>
    len_add!(len < opt spc cmt) >>
    sub_syss: map!(
      apply!(sub_sys_parser, offset + len, c.factory()),
      |(n,vec)| {
        len += n ;
        vec
      }
    ) >>
    len_add!(len < opt spc cmt) >>
    len_add!(len < char ')') >> (
      c.add_sys(sym, state, vec![], init, trans, sub_syss).map(
        |()| len
      )
    )
  )
}

/// Parses an item.
pub fn item_parser<'a>(
  bytes: & 'a [u8], c: & mut Context
) -> IResult<& 'a [u8], Result<(), Error>> {
  preceded!(
    bytes,
    opt!(multispace),
    alt!(
      map!(
        apply!(fun_dec_parser, 0, c),
        |res: Result<usize, Error>| res.map(|_| ())
      ) |
      map!(
        apply!(fun_def_parser, 0, c),
        |res: Result<usize, Error>| res.map(|_| ())
      ) |
      map!(
        apply!(prop_parser, 0, c),
        |res: Result<usize, Error>| res.map(|_| ())
      ) |
      map!(
        apply!(rel_parser, 0, c),
        |res: Result<usize, Error>| res.map(|_| ())
      ) |
      map!(
        apply!(sys_parser, 0, c),
        |res: Result<usize, Error>| res.map(|_| ())
      )
    )
  )
}

/// Parses a check.
pub fn check_parser<'a>(
  bytes: & 'a [u8], offset: usize, c: & Context
) -> IResult<& 'a [u8], Result<Spnd<Res>, Error>> {
  let mut len = 0 ;
  do_parse!(
    bytes,
    len_set!(len < char '(') >>
    len_add!(len < opt spc cmt) >>
    len_add!(len < bytes tag!("verify")) >>
    len_add!(len < spc cmt) >>
    sys: len_add!(
      len < spn thru apply!(sym_parser, offset + len, c.factory())
    ) >>
    len_add!(len < opt spc cmt) >>
    props: delimited!(
      len_add!(len < char '('),
      delimited!(
        len_add!(len < opt spc cmt),
        separated_list!(
          len_add!(len < spc cmt),
          len_add!(
            len < spn thru apply!(sym_parser, offset + len, c.factory())
          )
        ),
        len_add!(len < opt spc cmt)
      ),
      len_add!(len < char ')')
    ) >>
    len_add!(len < opt spc cmt) >>
    len_add!(len < char ')') >> (
      check_check(c, sys, props, None).map(
        |res| Spnd::len_mk(res, offset, len)
      )
    )
  )
}

/// Parses an atom.
pub fn atom_parser<'a>(
  bytes: & 'a [u8], offset: usize, f: & Factory
) -> IResult<& 'a [u8], Spnd<Atom>> {
  let mut len = 0 ;
  alt!(
    bytes,
    map!(
      len_add!(
        len < spn thru apply!(sym_parser, offset + len, f)
      ),
      |sym| Spnd::len_mk(Atom::Pos(sym), offset, len)
    ) |
    map!(
      delimited!(
        terminated!(
          len_add!(len < char '('),
          len_add!(len < opt spc cmt)
        ),
        do_parse!(
          len_add!(len < bytes tag!("not")) >>
          len_add!(len < spc cmt) >>
          sym: len_add!(
            len < spn thru apply!(sym_parser, offset + len, f)
          ) >> (
            Atom::Neg(sym)
          )
        ),
        preceded!(
          len_add!(len < opt spc cmt),
          len_add!(len < char ')')
        )
      ),
      |atom| Spnd::len_mk(atom, offset, len)
    )
  )
}

/// Parses a check with assumptions.
pub fn check_assuming_parser<'a>(
  bytes: & 'a [u8], offset: usize, c: & Context
) -> IResult<& 'a [u8], Result<Spnd<Res>, Error>> {
  let mut len = 0 ;
  do_parse!(
    bytes,
    len_set!(len < char '(') >>
    len_add!(len < opt spc cmt) >>
    len_add!(len < bytes tag!("verify-assuming")) >>
    len_add!(len < int space_comment) >>
    sys: apply!(sym_parser, offset + len, c.factory()) >>
    len_add!(len < opt spc cmt) >>
    props: delimited!(
      len_add!(len < char '('),
      delimited!(
        len_add!(len < opt spc cmt),
        separated_list!(
          len_add!(len < spc cmt),
          len_add!(
            len < spn thru apply!(sym_parser, offset + len, c.factory())
          )
        ),
        len_add!(len < opt spc cmt)
      ),
      len_add!(len < char ')')
    ) >>
    len_add!(len < opt spc cmt) >>
    atoms: delimited!(
      len_add!(len < char '('),
      delimited!(
        len_add!(len < opt spc cmt),
        separated_list!(
          len_add!(len < spc cmt),
          len_add!(
            len < spn apply!(atom_parser, offset + len, c.factory())
          )
        ),
        len_add!(len < opt spc cmt)
      ),
      len_add!(len < char ')')
    ) >>
    len_add!(len < opt spc cmt) >>
    len_add!(len < char ')') >> (
      check_check(c, sys, props, Some(atoms)).map(
        |res| Spnd::len_mk(res, offset, len)
      )
    )
  )
}

mk_parser!{
  #[doc = "Parses exit."]
  pub fn exit_parser(bytes, offset: usize) -> Result<Spnd<Res>, Error> {
    let mut len = 0 ;
    do_parse!(
      bytes,
      len_add!(len < char '(') >>
      len_add!(len < opt spc cmt) >>
      len_add!(len < bytes tag!("exit")) >>
      len_add!(len < opt spc cmt) >>
      len_add!(len < char ')') >> (
        Ok( Spnd::len_mk(Res::Exit, offset, len) )
      )
    )
  }
}

/// Parses a check with assumptions.
pub fn check_exit_parser<'a>(
  bytes: & 'a [u8], c: & Context
) -> IResult<& 'a [u8], Result<Spnd<Res>, Error>> {
  let mut len = 0 ;
  do_parse!(
    bytes,
    len_add!(len < opt spc cmt) >>
    res: alt!(
      apply!(check_parser, 0 + len, c) |
      apply!(check_assuming_parser, 0 + len, c) |
      apply!(exit_parser, 0 + len)
    ) >>
    len_add!(len < opt spc cmt) >> (res)
  )
}




