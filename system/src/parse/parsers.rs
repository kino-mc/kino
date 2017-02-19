// Copyright 2015 Adrien Champion. See the COPYRIGHT file at the top-level
// directory of this distribution.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use nom::IResult ;

use base::* ;
use super::Context ;
use super::{ Atom, Res } ;
use super::check::* ;
use term::Sym ;
use term::parsing::* ;
use term::parsing::vmt::* ;

use { Line, Error } ;

/// Alias type for parsing result.
pub type IRes<'a, T> = IResult<Bytes<'a>, T, InternalParseError> ;

/// Internal parse error, raised before it is matched against the actual text
/// input.
#[derive(Debug, PartialEq, Eq)]
pub struct InternalParseError {
  span: Spn,
  blah: String,
  notes: Vec< (Spn, String) >
}
impl InternalParseError {
  /// Creates an internal parse error.
  #[inline]
  pub fn mk(span: Spn, blah: String, notes: Vec< (Spn, String) >) -> Self {
    InternalParseError { span: span, blah: blah, notes: notes }
  }

  /// Transforms an `InternalParseError` in an `Error`.
  #[inline]
  pub fn to_parse_error(self, txt: & str, line_cnt: usize) -> Error {
    let InternalParseError { span, blah, notes } = self ;
    Error::parse_mk(
      line_extractor(txt, span, line_cnt), blah, notes.into_iter().map(
        |(spn, blah)| (line_extractor(txt, spn, line_cnt), blah)
      ).collect()
    )
  }

  /// Prints an internal parse error.
  #[cfg(test)]
  pub fn print(& self) {
    println!("{}: {}", self.span, self.blah) ;
    for & (ref span, ref blah) in self.notes.iter() {
      println!("| {}: {}", span, blah)
    }
  }
}
/// Extracts the line from a string where the `spn.bgn`th character is, the
/// number of that line in the text, and the subline highlighting the part
/// the span corresponds to.
fn line_extractor(
  txt: & str, spn: Spn, mut line_count: usize
) -> Line {
  debug_assert!(line_count > 0) ;
  debug_assert!(txt.len() >= spn.end) ;
  // println!{"line_count: {}", line_count}
  // println!{"extracting line from span {} from", spn}
  // for line in txt.lines() {
  //   println!{"  `{}`", line}
  // }
  let n = spn.bgn ;
  let mut bgn = 1 ;
  let mut end = 1 ;
  let mut gotit = false ;
  let mut cpt = 0 ;
  let mut offset = 1 ;
  for char in txt.chars() {
    cpt += 1 ;
    // println!() ;
    // println!("char : `{}`", char) ;
    // println!("  bgn: {}", bgn) ;
    // println!("  end: {}", end) ;
    // println!("  gotit: {}", gotit) ;
    // println!("  cpt: {}", cpt) ;
    // println!("  offset: {}", offset) ;
    // println!("  line_count: {}", line_count) ;
    debug_assert!(cpt > 0) ;
    match char {
      '\n' if gotit => {
        end = cpt ;
        break
      },
      '\n' => {
        line_count += 1 ;
        // Final nl of last line is not in new line.
        bgn = cpt + 1
      },
      _ if cpt == n => {
        gotit = true ;
        offset = cpt - bgn + 1
      },
      _ => (),
    }
  }
  debug_assert!(bgn > 0) ;
  debug_assert!(end > 0) ;
  debug_assert!(end < txt.len()) ;
  let line = if end >= bgn {
    (
      & txt[ (bgn - 1) .. (end - 1) ]
    ).to_string()
  } else { "".to_string() } ;
  let line_len = line.len() ;
  debug_assert!(offset > 0) ;
  Line::mk(
    line,
    format!(
      "{1: >0$}{3:^>2$}",
      offset - 1, "", ::std::cmp::min(spn.len(), line_len - offset), ""
    ),
    line_count,
    offset
  )
}


macro_rules! return_err (
  ($i:expr, |$s:pat, $d:pat, $n:pat| $e:expr, $submac:ident!( $($args:tt)* )
  ) => (
    match $submac!($i, $($args)*) {
      ::nom::IResult::Done(i, o) => ::nom::IResult::Done(i, o),
      ::nom::IResult::Error(
        ::nom::ErrorKind::Custom(
          InternalParseError { span: $s, blah: $d, notes: $n }
        )
      ) => {
        let (s, d, n) = $e ;
        return ::nom::IResult::Error(
          ::nom::ErrorKind::Custom(
            InternalParseError::mk(s, d, n).into()
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
    $bytes:expr, $submac:ident!($len:ident < trm ($t_offset:expr, $ctx:expr))
    ! at $span:expr, $blah:expr
  ) => (
    return_err!(
      $bytes,
      ::nom::ErrorKind::Custom(
        InternalParseError::mk(
          $span,
          $blah.into(),
          vec![]
        ).into()
      ),
      $submac!(
        $len < trm apply!(term_parser, $t_offset, $ctx.factory())
      )
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
          InternalParseError::mk(span, desc, notes).into()
        ) as ::nom::ErrorKind<InternalParseError>
      },
      $submac!($($args)*)
    )
  ) ;
}

/// Parses a signature, does **not** parse leading/trailing spaces/comments.
fn sig_parser(bytes: Bytes, offset: usize) -> IRes< Spnd<Sig> > {
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
fn args_parser<'a>(
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
          len_add!(len < opt spc cmt) >>
          typ: parse_or_fail!(
            len_add!(len < type (offset + len))
            ! at (offset + len), "in argument declaration"
          ) >>
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
fn fun_dec_parser<'a>(
  bytes: & 'a [u8], offset: usize, c: & mut Context
) -> IRes<'a, Spnd<Res>> {
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
        len < spn apply!(sig_parser, offset + len)
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
            InternalParseError::mk(
              sym_span.clone(), format!("{}", err), vec![
                (sym_span, "in this `declare-fun`".into())
              ]
            ).into()
          )
        ),
        Ok(()) => Spnd::len_mk(Res::Success, offset, len),
      }
    })
  )
}

/// Parses a function definition.
fn fun_def_parser<'a>(
  bytes: & 'a [u8], offset: usize, c: & mut Context
) -> IRes<'a, Spnd<Res>> {
  let mut len = 0 ;
  do_parse!(
    bytes,
    sym: parse_or_fail!(
      len_set!( len < sym (offset + len, c) )
      ! at (offset + len), "in `define-fun`"
    ) >>
    len_add!(len < opt spc cmt) >>
    args: return_err!(
      |s, d, mut vec| {
        vec.push(
          (sym.span.clone(), "in this `define-fun`".into())
        ) ;
        (s, d, vec)
      },
      len_add!(
        len < spn apply!(args_parser, offset + len, c)
      )
    ) >>
    len_add!(len < opt spc cmt) >>
    typ: parse_or_fail!(
      len_add!(
        len < type (offset + len)
      )
      ! at (offset + len), "in `define-fun`"
    ) >>
    len_add!(len < opt spc cmt) >>
    body: parse_or_fail!(
      len_add!(len < trm (offset + len, c))
      ! at sym.span.clone(), "parse error in body of `define-fun`"
    ) >> ({
      let sym_span = sym.span.clone() ;
      match c.add_fun_def(sym, args, typ, body) {
        Err(err) => return ::nom::IResult::Error(
          ::nom::ErrorKind::Custom(
            InternalParseError::mk(
              sym_span.clone(), format!("{}", err), vec![
                (sym_span, "in this `define-fun`".into())
              ]
            )
          )
        ),
        Ok(()) => Spnd::len_mk(Res::Success, offset, len),
      }
    })
  )
}

/// Parses a state property definition.
fn prop_parser<'a>(
  bytes: & 'a [u8], offset: usize, c: & mut Context
) -> IRes<'a, Spnd<Res>> {
  let mut len = 0 ;
  do_parse!(
    bytes,
    sym: parse_or_fail!(
      len_add!( len < sym (offset + len, c) )
      ! at (offset + len), "in `define-prop`"
    ) >>
    len_add!(len < opt spc cmt) >>
    sys: parse_or_fail!(
      len_add!( len < sym (offset + len, c) )
      ! at (offset + len), "for system name in `define-prop`"
    ) >>
    len_add!(len < opt spc cmt) >>
    body: parse_or_fail!(
      len_add!( len < trm (offset + len, c) )
      ! at sym.span.clone(), "parse error in body of `define-prop`"
    ) >> ({
      let sym_span = sym.span.clone() ;
      match c.add_prop(sym, sys, body) {
        Err(err) => return ::nom::IResult::Error(
          ::nom::ErrorKind::Custom(
            InternalParseError::mk(
              sym_span.clone(), format!("{}", err), vec![
                (sym_span, "in this `define-prop`".into())
              ]
            ).into()
          )
        ),
        Ok(()) => Spnd::len_mk(Res::Success, offset, len),
      }
    })
  )
}

/// Parses a state relation definition.
fn rel_parser<'a>(
  bytes: & 'a [u8], offset: usize, c: & mut Context
) -> IRes<'a, Spnd<Res>> {
  let mut len = 0 ;
  do_parse!(
    bytes,
    sym: parse_or_fail!(
      len_add!( len < sym (offset + len, c) )
      ! at (offset + len), "in `define-rel`"
    ) >>
    len_add!(len < opt spc cmt) >>
    sys: parse_or_fail!(
      len_add!( len < sym (offset + len, c) )
      ! at (offset + len), "for system name in `define-rel`"
    ) >>
    len_add!(len < opt spc cmt) >>
    body: parse_or_fail!(
      len_add!( len < trm (offset + len, c) )
      ! at sym.span.clone(), "parse error in body of `define-rel`"
    ) >> ({
      let sym_span = sym.span.clone() ;
      match c.add_rel(sym, sys, body) {
        Err(err) => return ::nom::IResult::Error(
          ::nom::ErrorKind::Custom(
            InternalParseError::mk(
              sym_span.clone(), format!("{}", err), vec![
                (sym_span, "in this `define-rel`".into())
              ]
            ).into()
          )
        ),
        Ok(()) => Spnd::len_mk(Res::Success, offset, len),
      }
    })
  )
}



fn sys_call_parser<'a>(
  bytes: & 'a [u8], offset: usize, c: & mut Context
) -> IRes<
  'a, Spnd<
    Vec< (Spnd<Sym>, Vec<TermAndDep>) >
  >
> {
  let mut len = 0 ;
  map!(
    bytes,
    delimited!(
      do_parse!(
        parse_or_fail!(
          len_set!(len < char '(')
          ! at (offset + len), "starting system calls"
        ) >>
        len_add!(len < opt spc cmt) >> (())
      ),
      many0!(
        do_parse!(
          len_add!(len < char '(') >>
          len_add!(len < opt spc cmt) >>
          sym: parse_or_fail!(
            len_add!(len < sym (offset + len, c))
            ! at (offset + len), "for system called's name"
          ) >>
          len_add!(len < opt spc cmt) >>
          params: many0!(
            len_add!(
              len < trm apply!(term_parser, offset + len, c.factory())
            )
          ) >>
          len_add!(len < opt spc cmt) >>
          parse_or_fail!(
            len_add!(len < char ')')
            ! at (offset + len),
            "closing system arguments, or another argument"
          ) >> (
            (sym, params)
          )
        )
      ),
      do_parse!(
        len_add!(len < opt spc cmt) >>
        parse_or_fail!(
          len_add!(len < char ')')
          ! at (offset + len), "closing system calls, or another system call"
        ) >> (())
      )
    ), |vec| Spnd::len_mk(vec, offset, len)
  )
}
fn sys_parser<'a>(
  bytes: & 'a [u8], offset: usize, c: & mut Context
) -> IRes<'a, Spnd<Res>> {
  let mut len = 0 ;
  do_parse!(
    bytes,
    sym: parse_or_fail!(
      len_add!(len < sym (offset + len, c))
      ! at (offset + len), "in `define-sys`"
    ) >>
    len_add!(len < opt spc cmt) >>
    state: return_err!(
      |s, d, mut vec| {
        vec.push(
          (sym.span.clone(), "in this `define-sys`".into())
        ) ;
        (s, d, vec)
      },
      len_add!(
        len < spn apply!(args_parser, offset + len, c)
      )
    ) >>
    len_add!(len < opt spc cmt) >>
    init: parse_or_fail!(
      len_add!(len < trm (offset + len, c))
      ! at sym.span.clone(), "parse error in initial term of `define-sys`"
    ) >>
    len_add!(len < opt spc cmt) >>
    trans: parse_or_fail!(
      len_add!(len < trm (offset + len, c))
      ! at sym.span.clone(), "parse error in transition term of `define-sys`"
    ) >>
    len_add!(len < opt spc cmt) >>
    sys_calls: return_err!(
      |s, d, mut vec| {
        vec.push(
          (sym.span.clone(), "in this `define-sys`".into())
        ) ;
        (s, d, vec)
      },
      len_add!(
        len < spn apply!(sys_call_parser, offset + len, c)
      )
    ) >> ({
      let sym_span = sym.span.clone() ;
      match c.add_sys(sym, state, vec![], init, trans, sys_calls) {
        Err(err) => return ::nom::IResult::Error(
          ::nom::ErrorKind::Custom(
            InternalParseError::mk(
              sym_span.clone(), format!("{}", err), vec![
                (sym_span, "in this `define-sys`".into())
              ]
            ).into()
          )
        ),
        Ok(()) => Spnd::len_mk(Res::Success, offset, len),
      }
    })
  )
}


fn atom_parser<'a>(
  bytes: & 'a [u8], offset: usize, c: & mut Context
) -> IRes<'a, Spnd<Atom>> {
  let mut len = 0 ;
  alt_complete!(
    bytes,
    fix_error!(
      InternalParseError,
      map!(
        len_add!(
          len < spn thru apply!(sym_parser, offset + len, c.factory())
        ), |sym| Spnd::len_mk(Atom::Pos(sym), offset, len)
      )
    ) |
    map!(
      delimited!(
        terminated!(
          len_add!(len < char '('),
          len_add!(len < opt spc cmt)
        ),
        do_parse!(
          parse_or_fail!(
            len_add!(len < tag "not")
            ! at (offset + len), "in atom negation"
          ) >>
          len_add!(len < opt spc cmt) >>
          sym: parse_or_fail!(
            len_add!(len < sym (offset + len, c))
            ! at (offset + len), "in atom negation"
          ) >> (
            Atom::Neg(sym)
          )
        ),
        preceded!(
          len_add!(len < opt spc cmt),
          parse_or_fail!(
            len_add!(len < char ')')
            ! at (offset + len), "closing atom negation"
          )
        )
      ), |atom| Spnd::len_mk(atom, offset, len)
    )
  )
}


fn verify_parser<'a>(
  bytes: & 'a [u8], offset: usize, c: & mut Context
) -> IRes<'a, Spnd<Res>> {
  let mut len = 0 ;
  do_parse!(
    bytes,
    sys: parse_or_fail!(
      len_add!(len < sym (offset + len, c))
      ! at (offset + len), "for system to check in `verify`"
    ) >>
    len_add!(len < opt spc cmt) >>
    props: delimited!(
      parse_or_fail!(
        len_add!(len < char '(')
        ! at (offset + len), "starting property/relation list"
      ),
      preceded!(
        len_add!(len < opt spc cmt),
        many0!(
          do_parse!(
            prop: len_add!(
              len < spn thru apply!(sym_parser, offset + len, c.factory())
            ) >>
            len_add!(len < opt spc cmt) >> (prop)
          )
        )
      ),
      parse_or_fail!(
        len_add!(len < char ')')
        ! at (offset + len), "closing property/relation list"
      )
    ) >> ({
      let sym_span = sys.span.clone() ;
      match check_check(c, sys, props, None) {
        Err(err) => return ::nom::IResult::Error(
          ::nom::ErrorKind::Custom(
            InternalParseError::mk(
              sym_span.clone(), format!("{}", err), vec![
                (sym_span, "in this `verify`".into())
              ]
            ).into()
          )
        ),
        Ok(res) => Spnd::len_mk(res, offset, len),
      }
    })
  )
}


fn verify_assuming_parser<'a>(
  bytes: & 'a [u8], offset: usize, c: & mut Context
) -> IRes<'a, Spnd<Res>> {
  let mut len = 0 ;
  do_parse!(
    bytes,
    sys: parse_or_fail!(
      len_add!(len < sym (offset + len, c))
      ! at (offset + len), "for system to check in `verify-assuming`"
    ) >>
    len_add!(len < opt spc cmt) >>
    props: delimited!(
      parse_or_fail!(
        len_add!(len < char '(')
        ! at (offset + len), "starting property/relation list"
      ),
      preceded!(
        len_add!(len < opt spc cmt),
        many0!(
          do_parse!(
            prop: len_add!(
              len < spn thru apply!(sym_parser, offset + len, c.factory())
            ) >>
            len_add!(len < opt spc cmt) >> (prop)
          )
        )
      ),
      parse_or_fail!(
        len_add!(len < char '(')
        ! at (offset + len), "closing property/relation list"
      )
    ) >>
    len_add!(len < opt spc cmt) >>
    atoms: delimited!(
      parse_or_fail!(
        len_add!(len < char '(')
        ! at (offset + len), "starting atom list"
      ),
      preceded!(
        len_add!(len < opt spc cmt),
        many0!(
          do_parse!(
            atom: len_add!(
              len < spn apply!(atom_parser, offset + len, c)
            ) >>
            len_add!(len < opt spc cmt) >> (atom)
          )
        )
      ),
      parse_or_fail!(
        len_add!(len < char '(')
        ! at (offset + len), "closing atom list"
      )
    ) >> ({
      let sym_span = sys.span.clone() ;
      match check_check(c, sys, props, Some(atoms)) {
        Err(err) => return ::nom::IResult::Error(
          ::nom::ErrorKind::Custom(
            InternalParseError::mk(
              sym_span.clone(), format!("{}", err), vec![
                (sym_span, "in this `verify-assuming`".into())
              ]
            ).into()
          )
        ),
        Ok(res) => Spnd::len_mk(res, offset, len),
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
    fix_error!(
      $bytes,
      InternalParseError,
      alt_complete!(
        $(
          do_parse!(
            $parser!( $($p_args)* ) >>
            res: return_err!( $and_then!($($then_args)*) ) >> (res)
          )
        )|+
      )
    )
  ) ;
}

/// Parses items.
pub fn item_parser<'a>(
  bytes: Bytes<'a>, offset: usize, ctx: & mut Context
) -> IRes<'a, Spnd<Res>> {
  let mut len = 0 ;
  delimited!(
    bytes,
    len_set!(len < opt spc cmt),
    do_parse!(
      parse_or_fail!(
        len_add!(len < char '(')
        ! at (offset + len), "opening VMT-LIB command"
      ) >>
      len_add!(len < opt spc cmt) >>
      res: parse_or_fail!(
        len_add!(
          len < spn thru try_parsers!(

            terminated!(
              len_add!(len < tag "declare-fun"),
              len_add!(len < opt spc cmt)
            ) >> apply!(fun_dec_parser, offset + len, ctx) |

            terminated!(
              len_add!(len < tag "define-fun"),
              len_add!(len < opt spc cmt)
            ) >> apply!(fun_def_parser, offset + len, ctx) |

            terminated!(
              len_add!(len < tag "define-prop"),
              len_add!(len < opt spc cmt)
            ) >> apply!(prop_parser, offset + len, ctx) |

            terminated!(
              len_add!(len < tag "define-rel"),
              len_add!(len < opt spc cmt)
            ) >> apply!(rel_parser, offset + len, ctx) |

            terminated!(
              len_add!(len < tag "define-sys"),
              len_add!(len < opt spc cmt)
            ) >> apply!(sys_parser, offset + len, ctx) |

            terminated!(
              len_add!(len < tag "verify-assuming"),
              len_add!(len < opt spc cmt)
            ) >> apply!(verify_assuming_parser, offset + len, ctx) |

            terminated!(
              len_add!(len < tag "verify"),
              len_add!(len < opt spc cmt)
            ) >> apply!(verify_parser, offset + len, ctx) |

            len_add!(len < tag "exit") >> map!(
              opt!(space_comment), |n: Option<usize>| {
                let res = Spnd::len_mk(
                  Res::Exit, offset + len - 4, 4
                ) ;
                len += n.unwrap_or(0) ;
                res
              }
            )

          )
        )
        ! at (offset + len),
        with (spn, str) => (
          spn, format!("expected VMT-LIB command, found `{}`", str), vec![]
        ),
        as Res
      ) >>
      len_add!(len < opt spc cmt) >>
      parse_or_fail!(
        len_add!(len < char ')')
        ! at (offset + len), "closing VMT-LIB command"
      ) >> (
        Spnd::len_mk(res.destroy().0, offset, len)
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
    use super::sig_parser ;
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
      Err(e) => {
        assert!(e.notes.is_empty()) ;
        assert_eq!( e.span, Spn::len_mk(13, 4) ) ;
        assert_eq!(
          e.blah,
          "expected `)` or type in signature declaration, found an identifier"
        ) ;
      },
      res => panic!("unexpected result: {:?}", res),
    }

    let txt = "Blah )" ;
    match try_parse_command!(sig_parser, 7, txt) {
      Err(e) => {
        assert!(e.notes.is_empty()) ;
        assert_eq!( e.span, Spn::len_mk(7, 4) ) ;
        assert_eq!(
          e.blah,
          "expected `(` starting signature declaration, found an identifier"
        ) ;
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
    use super::args_parser ;

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
      Err(e) => {
        e.print() ;
        assert!(e.notes.is_empty()) ;
        assert_eq!( e.span, Spn::len_mk(7, 4) ) ;
        assert_eq!(
          e.blah, "expected `(` opening argument list, found an identifier"
        ) ;
      },
      res => panic!("unexpected result: {:?}", res),
    }

    let txt = "( (7 Int) )" ;
    match try_parse_command!(args_parser, 7, ctx, txt) {
      Err(e) => {
        e.print() ;
        assert!(e.notes.is_empty()) ;
        assert_eq!( e.span, Spn::len_mk(10, 1) ) ;
        assert_eq!(
          e.blah, "expected symbol in argument declaration, found an integer"
        ) ;
      },
      res => panic!("unexpected result: {:?}", res),
    }

    let txt = "( (blah 3.0) )" ;
    match try_parse_command!(args_parser, 7, ctx, txt) {
      Err(e) => {
        e.print() ;
        assert!(e.notes.is_empty()) ;
        assert_eq!( e.span, Spn::len_mk(15, 3) ) ;
        assert_eq!(
          e.blah, "expected type in argument declaration, found a rational"
        ) ;
      },
      res => panic!("unexpected result: {:?}", res),
    }

    let txt = "( (blah Int) (blih Int Real) )" ;
    match try_parse_command!(args_parser, 7, ctx, txt) {
      Err(e) => {
        e.print() ;
        assert!(e.notes.is_empty()) ;
        assert_eq!( e.span, Spn::len_mk(30, 4) ) ;
        assert_eq!(
          e.blah,
          "expected `)` closing argument declaration in argument list, \
          found a type"
        ) ;
      },
      res => panic!("unexpected result: {:?}", res),
    }

    let txt = "( Int Blah )" ;
    match try_parse_command!(args_parser, 7, ctx, txt) {
      Err(e) => {
        e.print() ;
        assert!(e.notes.is_empty()) ;
        assert_eq!( e.span, Spn::len_mk(9, 3) ) ;
        assert_eq!(
          e.blah,
          "expected `)` closing argument list, or an argument \
          declaration, found a type"
        ) ;
      },
      res => panic!("unexpected result: {:?}", res),
    }
  }

  #[test]
  fn fun_decl_parser() {
    use super::item_parser ;

    let mut ctx = get_context() ;

    let txt = "(declare-fun prout (Int) Bool)" ;
    match try_parse_command!(item_parser, 7, ctx, txt) {
      Err(e) => {
        e.print() ;
        panic!("unexpected result")
      },
      Ok(res) => assert_eq!( res.1.to_span(), Spn::len_mk(7, 30) ),
    }

    let txt = "(declare-fun blah (Blah) Bool)" ;
    match try_parse_command!(item_parser, 7, ctx, txt) {
      Err(mut e) => {
        e.print() ;
        assert_eq!( e.span, Spn::len_mk(26, 4) ) ;
        assert_eq!(
          e.blah,
          "expected `)` or type in signature declaration, found an identifier"
        ) ;
        assert_eq!(
          e.notes.pop(),
          Some(
            (Spn::len_mk(20, 4), "in this `declare-fun`".to_string())
          )
        )
      },
      Ok(res) => panic!("unexpected result: {:?}", res),
    }

    let txt = "(declare-fun blah (Int) Blah)" ;
    match try_parse_command!(item_parser, 7, ctx, txt) {
      Err(e) => {
        e.print() ;
        assert_eq!( e.span, Spn::len_mk(31, 4) ) ;
        assert_eq!(
          e.blah,
          "expected type in `declare-fun`, \
          found an identifier".to_string()
        ) ;
        assert!(
          e.notes.is_empty()
        )
      },
      Ok(res) => panic!("unexpected result: {:?}", res),
    }
  }

  #[test]
  fn fun_def_parser() {
    use super::item_parser ;

    let mut ctx = get_context() ;

    let txt = "(define-fun prout ( (x Int) ) Bool (>= x 0))" ;
    match try_parse_command!(item_parser, 7, ctx, txt) {
      Err(e) => {
        e.print() ;
        panic!("unexpected result")
      },
      Ok(res) => assert_eq!( res.1.to_span(), Spn::len_mk(7, 44) ),
    }

    let txt = "(define-fun prout ( Int) Bool)" ;
    match try_parse_command!(item_parser, 7, ctx, txt) {
      Err(mut e) => {
        e.print() ;
        assert_eq!( e.span, Spn::len_mk(27, 3) ) ;
        assert_eq!(
          e.blah,
          "expected `)` closing argument list, \
          or an argument declaration, found a type"
        ) ;
        assert_eq!(
          e.notes.pop(),
          Some(
            (Spn::len_mk(19, 5), "in this `define-fun`".to_string())
          )
        )
      },
      Ok(res) => panic!("unexpected result: {:?}", res),
    }
  }

  #[test]
  fn sys_parser() {
    use super::item_parser ;

    let mut ctx = get_context() ;

    let txt = "\
(define-sys prout
  ;; State.
  ( (x Int) )
  ;; Init.
  (>= (_curr x) 0)
  ;; Trans.
  (> (_ next x) (_ curr x))
  ;; No calls.
  ()
)\
    " ;
    match try_parse_command!(item_parser, 7, ctx, txt) {
      Err(e) => {
        e.print() ;
        panic!("unexpected result")
      },
      Ok(res) => assert_eq!( res.1.to_span(), Spn::len_mk(7, 135) ),
    }

    let txt = "\
(define-sys prout
  ;; State.
  ( (Int) )
  ;; Init.
  (>= (_curr x) 0)
  ;; Trans.
  (> (_ next x) (_ curr x))
  ;; No calls.
  ()
)\
    " ;
    match try_parse_command!(item_parser, 7, ctx, txt) {
      Err(mut e) => {
        e.print() ;
        assert_eq!( e.span, Spn::len_mk(45, 1) ) ;
        assert_eq!(
          e.blah,
          "expected type in argument declaration, found `)`"
        ) ;
        assert_eq!(
          e.notes.pop(),
          Some(
            (Spn::len_mk(19, 5), "in this `define-sys`".to_string())
          )
        )
      },
      Ok(res) => panic!("unexpected result: {:?}", res),
    }
  }

  #[test]
  fn prop_parser() {
    use super::item_parser ;

    let mut ctx = get_context() ;

    let txt = "\
(define-sys prout
  ;; State.
  ( (x Int) )
  ;; Init.
  (>= (_curr x) 0)
  ;; Trans.
  (> (_ next x) (_ curr x))
  ;; No calls.
  ()
)\
    " ;
    match try_parse_command!(item_parser, 7, ctx, txt) {
      Err(e) => {
        e.print() ;
        panic!("unexpected result")
      },
      Ok(res) => assert_eq!( res.1.to_span(), Spn::len_mk(7, 135) ),
    }

    let txt = "(define-prop blah prout (= (_ curr x) 0))" ;
    match try_parse_command!(item_parser, 7, ctx, txt) {
      Err(e) => {
        e.print() ;
        panic!("unexpected result")
      },
      Ok(res) => assert_eq!( res.1.to_span(), Spn::len_mk(7, 41) ),
    }

    let txt = "(define-prop blah prout)" ;
    match try_parse_command!(item_parser, 7, ctx, txt) {
      Err(e) => {
        e.print() ;
        assert_eq!( e.span, Spn::len_mk(20, 4) ) ;
        assert_eq!(
          e.blah,
          "parse error in body of `define-prop`"
        ) ;
        assert!(e.notes.is_empty())
      },
      Ok(res) => panic!("unexpected result: {:?}", res),
    }
  }

  #[test]
  fn rel_parser() {
    use super::item_parser ;

    let mut ctx = get_context() ;

    let txt = "\
(define-sys prout
  ;; State.
  ( (x Int) )
  ;; Init.
  (>= (_curr x) 0)
  ;; Trans.
  (> (_ next x) (_ curr x))
  ;; No calls.
  ()
)\
    " ;
    match try_parse_command!(item_parser, 7, ctx, txt) {
      Err(e) => {
        e.print() ;
        panic!("unexpected result")
      },
      Ok(res) => assert_eq!( res.1.to_span(), Spn::len_mk(7, 135) ),
    }

    let txt = "(define-rel blah prout (= (_ curr x) (_next x)))" ;
    match try_parse_command!(item_parser, 7, ctx, txt) {
      Err(e) => {
        e.print() ;
        panic!("unexpected result")
      },
      Ok(res) => assert_eq!( res.1.to_span(), Spn::len_mk(7, 48) ),
    }

    let txt = "(define-rel blah prout)" ;
    match try_parse_command!(item_parser, 7, ctx, txt) {
      Err(e) => {
        e.print() ;
        assert_eq!( e.span, Spn::len_mk(19, 4) ) ;
        assert_eq!(
          e.blah,
          "parse error in body of `define-rel`"
        ) ;
        assert!(e.notes.is_empty())
      },
      Ok(res) => panic!("unexpected result: {:?}", res),
    }
  }
}