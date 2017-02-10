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
use parse_errors ;
use term::{ Type, Sym, Factory } ;
use term::parsing::* ;
use term::parsing::vmt::* ;

mk_parser!{
  #[doc = "Parses a signature."]
  pub fn sig_parser(bytes, offset: usize) -> Spnd<Sig> {
    let mut len = 0 ;
    do_parse!(
      bytes,
      len_set!(len < char '(') >>
      len_add!(len < opt spc cmt) >>
      args: separated_list!(
        len_add!(len < spc cmt),
        map!(
          apply!(type_parser, offset + len), |t: Spnd<Type>| {
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
            len < spn thru apply!(sym_parser, offset + len, f)
          ) >>
          len_add!(len < spc cmt) >>
          typ: len_add!(
            len < spn thru apply!(type_parser, offset + len)
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
pub fn fun_dec_parser<'a>(
  bytes: & 'a [u8], offset: usize, c: & mut Context
) -> IResult<& 'a [u8], Result<usize, Error>> {
  let mut len = 0 ;
  do_parse!(
    bytes,
    len_set!(len < char '(') >>
    len_add!(len < opt spc cmt) >>
    len_add!(len < bytes tag!("declare-fun")) >>
    len_add!(len < opt spc cmt) >>
    sym: len_add!(
      len < spn thru apply!(sym_parser, offset + len, c.factory())
    ) >>
    len_add!(len < opt spc cmt) >>
    sig: len_add!(
      len < spn apply!(sig_parser, offset + len)
    ) >>
    len_add!(len < opt spc cmt) >>
    typ: len_add!(
      len < spn thru apply!(type_parser, offset + len)
    ) >>
    len_add!(len < opt spc cmt) >>
    len_add!(len < char ')') >> (
      c.add_fun_dec(sym, sig, typ).map(|()| len)
    )
  )
}

/// Parses a function definition.
pub fn fun_def_parser<'a>(
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
pub fn prop_parser<'a>(
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
pub fn rel_parser<'a>(
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

/// Parses the calls inside a system definition.
pub fn sub_sys_parser<'a>(
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
                len < trm apply!(term_parser, offset + len, f)
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
pub fn sys_parser<'a>(
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
) -> IResult<& 'a [u8], Result<(), ::parse_errors::Error>> {
  preceded!(
    bytes,
    opt!(multispace),
    map!(
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
      ),
      |res: Result<(), Error>| res.map_err(
        |e| ::parse_errors::ErrorKind::OldError(e).into()
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
) -> IResult<& 'a [u8], Result<Spnd<Res>, parse_errors::Error>> {
  let mut len = 0 ;
  do_parse!(
    bytes,
    len_add!(len < opt spc cmt) >>
    res: alt!(
      apply!(check_parser, 0 + len, c) |
      apply!(check_assuming_parser, 0 + len, c) |
      apply!(exit_parser, 0 + len)
    ) >>
    len_add!(len < opt spc cmt) >> (
      res.map_err(|e| parse_errors::ErrorKind::OldError(e).into())
    )
  )
}

// #[cfg(test)]
// mod items {
//   use super::* ;
//   use parse::Context ;
//   use term::parsing::* ;
//   use term::Factory ;

//   fn get_ctx() -> Context {
//     let factory = Factory::mk() ;
//     Context::mk(factory, 100)
//   }

//   #[test]
//   fn fun_dec() {
//     let mut ctx = get_ctx() ;
//     let txt = "\
// (declare-fun blah ( Int ) Int)\
//     " ;
//     try_parse_command!(ctx, 0, fun_dec_parser, txt)
//   }
// }

/// Alias type for parsing result output.
pub type PRes<T> = Result<T, parse_errors::Error> ;

/// Alias type for parsing result.
pub type IRes<'a, T> = IResult<Bytes<'a>, T, parse_errors::Error> ;

macro_rules! return_err (
  ($i:expr, |$s:pat, $d:pat, $n:pat| $e:expr, $submac:ident!( $($args:tt)* )
  ) => (
    match $submac!($i, $($args)*) {
      ::nom::IResult::Done(i, o) => ::nom::IResult::Done(i, o),
      ::nom::IResult::Error(
        ::nom::ErrorKind::Custom(
          ::parse_errors::Error(
            ::parse_errors::ErrorKind::ParseError($s, $d, $n),
            _
          )
        )
      ) => {
        let (s, d, n) = $e ;
        return ::nom::IResult::Error(
          ::nom::ErrorKind::Custom(
            ::parse_errors::ErrorKind::ParseError(s, d, n).into()
          )
        )
      },
      ::nom::IResult::Error(e) => return ::nom::IResult::Error(e),
      ::nom::IResult::Incomplete(e) => return ::nom::IResult::Incomplete(e),
    }
  ) ;
  ($i:expr, $code:expr, $submac:ident!( $($args:tt)* )) => (
    match $submac!($i, $($args)*) {
      ::nom::IResult::Done(i, o) => ::nom::IResult::Done(i, o),
      _ => return ::nom::IResult::Error($code),
    }
  ) ;
  ($i:expr, $submac:ident!( $($args:tt)* )
  ) => (
    match $submac!($i, $($args)*) {
      ::nom::IResult::Done(i, o) => ::nom::IResult::Done(i, o),
      ::nom::IResult::Error(e) => return ::nom::IResult::Error(e),
      ::nom::IResult::Incomplete(e) => return ::nom::IResult::Incomplete(e),
    }
  ) ;
  ($i:expr, $code:expr, $f:expr) => (
    return_err!($i, $code, call!($f))
  ) ;
);

/// Parses something or fails after calling the token parser.
macro_rules! parse_or_fail {
  (
    $bytes:expr, $submac:ident!($len:ident < char $c:expr)
    ! at $offset:expr, $blah:expr
  ) => (
    parse_or_fail!(
      $bytes, $submac!($len < char $c)
      ! at $offset, with (span, desc) => (
        span, format!(
          "expected `{}` {}, found {}", $c, $blah, desc
        ), vec![]
      ), as ()
    )
  ) ;
  (
    $bytes:expr, $submac:ident!($len:ident < tag $s:expr)
    ! at $offset:expr, $blah:expr
  ) => (
    parse_or_fail!(
      $bytes, $submac!($len < tag $s)
      ! at $offset, with (span, desc) => (
        span, format!(
          "expected `{}` {}, found {}", $s, $blah, desc
        ), vec![]
      ), as ()
    )
  ) ;
  (
    $bytes:expr, $submac:ident!($len:ident < type ($t_offset:expr))
    ! at $offset:expr, $blah:expr
  ) => (
    parse_or_fail!(
      $bytes, $submac!(
        $len < spn thru apply!(type_parser, $t_offset)
      )! at $offset, with (span, desc) => (
        span, format!(
          "expected type {}, found {}", $blah, desc
        ), vec![]
      ), as Spnd<Type>
    )
  ) ;
  (
    $bytes:expr, $submac:ident!($len:ident < sym ($t_offset:expr, $ctx:expr))
    ! at $offset:expr, $blah:expr
  ) => (
    parse_or_fail!(
      $bytes, $submac!(
        $len < spn thru apply!(sym_parser, $t_offset, $ctx.factory())
      )! at $offset, with (span, desc) => (
        span, format!(
          "expected symbol {}, found {}", $blah, desc
        ), vec![]
      ), as Spnd<Sym>
    )
  ) ;
  (
    $bytes:expr, $submac:ident!($($args:tt)*)
    ! at $offset:expr, with $err_args:pat => $e:expr, as $t:ty
  ) => (
    return_err!(
      $bytes,
      {
        let $err_args = token_parser($bytes, $offset).unwrap().1 ;
        let (span, desc, notes) = $e ;
        ::nom::ErrorKind::Custom(
          ::parse_errors::ErrorKind::ParseError(span, desc, notes).into()
        ) as ::nom::ErrorKind<
          ::parse_errors::Error
        >
      },
      $submac!($($args)*)
    )
  ) ;
}

/// Parses a signature, does **not** parse leading/trailing spaces/comments.
pub fn _sig_parser(bytes: Bytes, offset: usize) -> IRes< Spnd<Sig> > {
  let mut len = 0 ;
  do_parse!(
    bytes,
    parse_or_fail!(
      len_set!(len < char '(')
      ! at (offset + len), "starting signature declaration"
    ) >>
    len_add!(len < opt spc cmt) >>
    args: many0!(
      terminated!(
        len_add!(
          len < spn thru apply!(type_parser, offset + len)
        ),
        len_add!(len < opt spc cmt)
      )
    ) >>
    parse_or_fail!(
      len_add!(len < char ')')
      ! at (offset + len), "or type in signature declaration"
    ) >> (
      Spnd::len_mk(Sig::mk(args), offset, len)
    )
  )
}

/// Parses some arguments, does **not** parse leading/trailing
/// spaces/comments.
fn _args_parser<'a>(
  bytes: Bytes<'a>, offset: usize, c: & mut Context
) -> IRes<'a, Spnd<Args>> {
  let mut len = 0 ;
  do_parse!(
    bytes,
    parse_or_fail!(
      len_set!(len < char '(')
      ! at (offset + len), "opening argument list"
    ) >>
    len_add!(len < opt spc cmt) >>
    args: many0!(
      delimited!(
        len_add!(len < char '('),
        do_parse!(
          len_add!(len < opt spc cmt) >>
          sym: parse_or_fail!(
            len_add!(len < sym (offset + len, c))
            ! at (offset + len), "in argument declaration"
          ) >>
          // sym: len_add!(
          //   len < spn thru apply!(sym_parser, offset + len, f)
          // ) >>
          len_add!(len < spc cmt) >>
          typ: parse_or_fail!(
            len_add!(len < type (offset + len))
            ! at (offset + len), "in argument declaration"
          ) >>
          // typ: len_add!(
          //   len < spn thru apply!(type_parser, offset + len)
          // ) >>
          len_add!(len < opt spc cmt) >> 
          parse_or_fail!(
            len_add!(len < char ')')
            ! at (offset + len),
            "closing argument declaration in argument list"
          ) >> (
            (sym, typ)
          )
        ),
        len_add!(len < opt spc cmt)
      )
    ) >>
    parse_or_fail!(
      len_add!(len < char ')')
      ! at (offset + len), "closing argument list, or an argument declaration"
    ) >> (
      Spnd::len_mk(Args::mk(args), offset, len)
    )
  )
}

/// Parses a function declaration.
pub fn _fun_dec_parser<'a>(
  bytes: & 'a [u8], offset: usize, c: & mut Context
) -> IRes<'a, Spnd<()>> {
  let mut len = 0 ;
  println!("offset: {}", offset) ;
  do_parse!(
    bytes,
    sym: parse_or_fail!(
      len_set!( len < sym (offset + len, c) )
      ! at (offset + len), "in `declare-fun`"
    ) >>
    len_add!(len < opt spc cmt) >>
    sig: return_err!(
      |s, d, mut vec| {
        vec.push(
          (sym.span.clone(), "in this `declare-fun`".into())
        ) ;
        (s, d, vec)
      },
      len_add!(
        len < spn apply!(_sig_parser, offset + len)
      )
    ) >>
    len_add!(len < opt spc cmt) >>
    typ: parse_or_fail!(
      len_add!(
        len < type (offset + len)
      )
      ! at (offset + len), "in `declare-fun`"
    ) >> ({
      let sym_span = sym.span.clone() ;
      match c.add_fun_dec(sym, sig, typ) {
        Err(err) => return ::nom::IResult::Error(
          ::nom::ErrorKind::Custom(
            ::parse_errors::ErrorKind::ParseError(
              sym_span.clone(), format!("{}", err), vec![
                (sym_span, "in this `declare-fun`".into())
              ]
            ).into()
          )
        ),
        Ok(()) => Spnd::len_mk((), offset, len),
      }
    })
  )
}

/// Tries to run `$parser`:
///
/// - if successful, runs `$and_then` without backtracking
/// - otherwise, moves on to the next `$parser`.
macro_rules! try_parsers {
  (
    $bytes:expr,
    $(
      $parser:ident!( $($p_args:tt)* )
      >> $and_then:ident!( $($then_args:tt)* )
    )|+
  ) => (
    alt_complete!(
      $bytes,
      $(
        do_parse!(
          $parser!( $($p_args)* ) >>
          res: return_err!( $and_then!($($then_args)*) ) >> (res)
        )
      )|+
    )
  ) ;
}

/// Parses items.
pub fn _item_parser<'a>(
  bytes: Bytes<'a>, offset: usize, ctx: & mut Context
) -> IRes<'a, Spnd<Res>> {
  let mut len = 0 ;
  delimited!(
    bytes,
    len_set!(len < opt spc cmt),
    do_parse!(
      parse_or_fail!(
        len_add!(len < char '(')
        ! at (offset + len), "opening command"
      ) >>
      len_add!(
        len < spn thru try_parsers!(

          terminated!(
            len_add!(len < tag "declare-fun"),
            len_add!(len < opt spc cmt)
          ) >> apply!(_fun_dec_parser, offset + len, ctx)

          // terminated!(
          //   len_add!(len < tag "define-fun"),
          //   len_add!(len < opt spc cmt)
          // ) >> apply!(_sig_parser, offset + len) |

          // terminated!(
          //   len_add!(len < tag "define-prop"),
          //   len_add!(len < opt spc cmt)
          // ) >> apply!(_sig_parser, offset + len) |

          // terminated!(
          //   len_add!(len < tag "define-rel"),
          //   len_add!(len < opt spc cmt)
          // ) >> apply!(_sig_parser, offset + len) |

          // terminated!(
          //   len_add!(len < tag "define-sys"),
          //   len_add!(len < opt spc cmt)
          // ) >> apply!(_sig_parser, offset + len)

        )
      ) >>
      parse_or_fail!(
        len_add!(len < char ')')
        ! at (offset + len), "closing command"
      ) >> (
        Spnd::len_mk(Res::Exit, offset, len)
      )
    ),
    len_add!(len < opt spc cmt)
  )
}



#[cfg(test)]
mod test {
  use term::parsing::* ;
  use term::* ;
  use ctxt::* ;

  macro_rules! try_parse_command {
    (
      $parser:ident, $offset:expr, $input:expr
    ) => (
      try_parse_command!(
        $parser($input.as_bytes(), $offset),
        $input
      )
    ) ;
    (
      $parser:ident, $offset:expr, $ctx:expr, $input:expr
    ) => (
      try_parse_command!(
        $parser($input.as_bytes(), $offset, & mut $ctx),
        $input
      )
    ) ;
    (
      $e:expr, $input:expr
    ) => ({
      println!("| parsing text:") ;
      for line in $input.lines() {
        println!("| > `{}`", line)
      }
      match $e {
        ::nom::IResult::Done(rest, res) => {
          println!("| success") ;
          Ok( (rest, res) )
        },
        ::nom::IResult::Error(
          ::nom::ErrorKind::Custom(e)
        ) => Err(e),
        ::nom::IResult::Error(e) => panic!("error: {:?}", e),
        ::nom::IResult::Incomplete(n) => panic!("incomplete: {:?}", n),
      }
    }) ;
  }

  #[test]
  fn sig_parser() {
    use super::_sig_parser as sig_parser ;
    let txt = "(Int Bool)" ;
    let res = try_parse_command!(sig_parser, 7, txt).unwrap().1 ;
    let (sig, spn) = res.destroy() ;
    assert_eq!{ spn, Spn::len_mk(7, 10) }
    let mut iter = sig.types().iter() ;
    assert_eq!{
      iter.next(), Some(
        & Spnd::len_mk(Type::Int, 8, 3)
      )
    }
    assert_eq!{
      iter.next(), Some(
        & Spnd::len_mk(Type::Bool, 12, 4)
      )
    }

    let txt = "(  Int   Bool )" ;
    let res = try_parse_command!(sig_parser, 7, txt).unwrap().1 ;
    let (sig, spn) = res.destroy() ;
    assert_eq!{ spn, Spn::len_mk(7, 15) }
    let mut iter = sig.types().iter() ;
    assert_eq!{
      iter.next(), Some(
        & Spnd::len_mk(Type::Int, 10, 3)
      )
    }
    assert_eq!{
      iter.next(), Some(
        & Spnd::len_mk(Type::Bool, 16, 4)
      )
    }

    let txt = "( Int Blah )" ;
    match try_parse_command!(sig_parser, 7, txt) {
      Err(
        ::parse_errors::Error(
          ::parse_errors::ErrorKind::ParseError(spn, desc, vec), _
        )
      ) => {
        assert!(vec.is_empty()) ;
        assert_eq!( spn, Spn::len_mk(13, 4) ) ;
        assert_eq!( desc, "expected `)` or type in signature declaration, found an identifier") ;
      },
      res => panic!("unexpected result: {:?}", res),
    }

    let txt = "Blah )" ;
    match try_parse_command!(sig_parser, 7, txt) {
      Err(
        ::parse_errors::Error(
          ::parse_errors::ErrorKind::ParseError(spn, desc, vec), _
        )
      ) => {
        assert!(vec.is_empty()) ;
        assert_eq!( spn, Spn::len_mk(7, 4) ) ;
        assert_eq!( desc, "expected `(` starting signature declaration, found an identifier") ;
      },
      res => panic!("unexpected result: {:?}", res),
    }
  }

  fn get_context() -> Context {
    let factory = Factory::mk() ;
    Context::mk(factory, 100)
  }

  #[test]
  fn args_parser() {
    use super::_args_parser as args_parser ;

    let mut ctx = get_context() ;

    let blah = ctx.factory().sym("blah") ;
    let blih = ctx.factory().sym("blih") ;

    let txt = "((blah Int) (blih Bool))" ;
    let res = try_parse_command!(args_parser, 7, ctx, txt).unwrap().1 ;
    let (args, spn) = res.destroy() ;
    assert_eq!{ spn, Spn::len_mk(7, 24) }
    let mut iter = args.args().iter() ;
    assert_eq!{
      iter.next(), Some(
        & (
          Spnd::len_mk(blah.clone(), 9, 4),
          Spnd::len_mk(Type::Int, 14, 3)
        )
      )
    }
    assert_eq!{
      iter.next(), Some(
        & (
          Spnd::len_mk(blih.clone(), 20, 4),
          Spnd::len_mk(Type::Bool, 25, 4)
        )
      )
    }

    let txt = "(  ( blah  Int )(  blih Bool)  )" ;
    let res = try_parse_command!(args_parser, 7, ctx, txt).unwrap().1 ;
    let (args, spn) = res.destroy() ;
    assert_eq!{ spn, Spn::len_mk(7, 32) }
    let mut iter = args.args().iter() ;
    assert_eq!{
      iter.next(), Some(
        & (
          Spnd::len_mk(blah.clone(), 12, 4),
          Spnd::len_mk(Type::Int, 18, 3)
        )
      )
    }
    assert_eq!{
      iter.next(), Some(
        & (
          Spnd::len_mk(blih.clone(), 26, 4),
          Spnd::len_mk(Type::Bool, 31, 4)
        )
      )
    }

    let txt = "Blah )" ;
    match try_parse_command!(args_parser, 7, ctx, txt) {
      Err(
        ::parse_errors::Error(
          ::parse_errors::ErrorKind::ParseError(spn, desc, vec), _
        )
      ) => {
        assert!(vec.is_empty()) ;
        assert_eq!( spn, Spn::len_mk(7, 4) ) ;
        assert_eq!(
          desc, "expected `(` opening argument list, found an identifier"
        ) ;
      },
      res => panic!("unexpected result: {:?}", res),
    }

    let txt = "( (7 Int) )" ;
    match try_parse_command!(args_parser, 7, ctx, txt) {
      Err(
        ::parse_errors::Error(
          ::parse_errors::ErrorKind::ParseError(spn, desc, vec), _
        )
      ) => {
        assert!(vec.is_empty()) ;
        assert_eq!( spn, Spn::len_mk(10, 1) ) ;
        assert_eq!(
          desc, "expected symbol in argument declaration, found an integer"
        ) ;
      },
      res => panic!("unexpected result: {:?}", res),
    }

    let txt = "( (blah 3.0) )" ;
    match try_parse_command!(args_parser, 7, ctx, txt) {
      Err(
        ::parse_errors::Error(
          ::parse_errors::ErrorKind::ParseError(spn, desc, vec), _
        )
      ) => {
        assert!(vec.is_empty()) ;
        assert_eq!( spn, Spn::len_mk(15, 3) ) ;
        assert_eq!(
          desc, "expected type in argument declaration, found a rational"
        ) ;
      },
      res => panic!("unexpected result: {:?}", res),
    }

    let txt = "( (blah Int) (blih Int Real) )" ;
    match try_parse_command!(args_parser, 7, ctx, txt) {
      Err(
        ::parse_errors::Error(
          ::parse_errors::ErrorKind::ParseError(spn, desc, vec), _
        )
      ) => {
        assert!(vec.is_empty()) ;
        assert_eq!( spn, Spn::len_mk(30, 4) ) ;
        assert_eq!(
          desc, "expected `)` closing argument declaration in argument list, \
          found a type"
        ) ;
      },
      res => panic!("unexpected result: {:?}", res),
    }

    let txt = "( Int Blah )" ;
    match try_parse_command!(args_parser, 7, ctx, txt) {
      Err(
        ::parse_errors::Error(
          ::parse_errors::ErrorKind::ParseError(spn, desc, vec), _
        )
      ) => {
        assert!(vec.is_empty()) ;
        assert_eq!( spn, Spn::len_mk(9, 3) ) ;
        assert_eq!(
          desc, "expected `)` closing argument list, or an argument \
          declaration, found a type"
        ) ;
      },
      res => panic!("unexpected result: {:?}", res),
    }
  }

  #[test]
  fn fun_decl_parser() {
    use super::_item_parser as item_parser ;

    let mut ctx = get_context() ;

    let txt = "(declare-fun prout (Int) Bool)" ;
    match try_parse_command!(item_parser, 7, ctx, txt) {
      Err(e) => {
        println!("error:") ;
        for e in e.iter() {
          println!("> {}", e)
        }
        panic!("unexpected result")
      },
      Ok(res) => assert_eq!( res.1.to_span(), Spn::len_mk(7, 30) ),
    }

    let txt = "(declare-fun blah (Blah) Bool)" ;
    match try_parse_command!(item_parser, 7, ctx, txt) {
      Err(
        ::parse_errors::Error(
          ::parse_errors::ErrorKind::ParseError(spn, desc, mut vec), _
        )
      ) => {
        assert_eq!( spn, Spn::len_mk(26, 4) ) ;
        assert_eq!(
          desc,
          "expected `)` or type in signature declaration, found an identifier"
        ) ;
        assert_eq!(
          vec.pop(),
          Some(
            (Spn::len_mk(20, 4), "in this `declare-fun`".to_string())
          )
        )
      },
      Err(e) => {
        println!("error:") ;
        for e in e.iter() {
          println!("> {}", e)
        }
        panic!("unexpected result")
      },
      Ok(res) => panic!("unexpected result: {:?}", res),
    }

    let txt = "(declare-fun blah (Int) Blah)" ;
    match try_parse_command!(item_parser, 7, ctx, txt) {
      Err(
        ::parse_errors::Error(
          ::parse_errors::ErrorKind::ParseError(spn, desc, vec), _
        )
      ) => {
        assert_eq!( spn, Spn::len_mk(31, 4) ) ;
        assert_eq!(
          desc,
          "expected type in `declare-fun`, \
          found an identifier".to_string()
        ) ;
        assert!(
          vec.is_empty()
        )
      },
      Err(e) => {
        println!("error:") ;
        for e in e.iter() {
          println!("> {}", e)
        }
        panic!("unexpected result")
      },
      Ok(res) => panic!("unexpected result: {:?}", res),
    }
  }
}