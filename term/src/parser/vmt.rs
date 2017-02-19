// Copyright 2015 Adrien Champion. See the COPYRIGHT file at the top-level
// directory of this distribution.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! Parsers for the `vmt` format.

use std::str ;
use std::collections::HashSet ;
use std::fmt ;

use nom::{ IResult } ;

use base::State ;
use typ::Type ;
use cst::Cst ;
use sym::Sym ;
use var::{ VarMaker, Var } ;
use term::{ Term, Operator } ;
use factory::Factory ;

use super::{
  Spn, Spnd, Bytes,
  type_parser,
  space_comment,
  simple_symbol_head, simple_symbol_tail,
  operator_parser,
  quantifier_parser, Quantifier
} ;

/// Result of VMT parsing.
#[derive(Clone,Debug)]
pub struct TermAndDep {
  /// The term parsed.
  pub term: Term,
  /// The function symbol applications in the term.
  pub apps: HashSet<Sym>,
  /// The variables in the term.
  pub vars: HashSet<Var>,
  /// Types found in the term.
  /// Does **not** include the types of variables.
  pub types: HashSet<Type>,
  /// Whether the term is linear.
  pub linear: bool,
  /// Whether the term is quantifier-free.
  pub qf: bool,
  /// The span of the term.
  pub span: Spn,
}
impl fmt::Display for TermAndDep {
  fn fmt(& self, fmt: & mut fmt::Formatter) -> fmt::Result {
    self.term.fmt(fmt)
  }
}
impl TermAndDep {
  /// Creates a term with dependencies from a variable.
  pub fn var(
    factory: & Factory, var: Var, span: Spn
  ) -> Self {
    let term: Term = factory.mk_var(var.clone()) ;
    let mut vars = HashSet::new() ;
    vars.insert(var) ;
    TermAndDep {
      term: term,
      apps: HashSet::new(),
      vars: vars,
      types: HashSet::new(),
      linear: true,
      qf: true,
      span: span,
    }
  }
  /// Creates a term with dependencies from a constant.
  pub fn cst(
    factory: & Factory, cst: Cst, span: Spn
  ) -> Self {
    use term::CstMaker ;
    let mut types = HashSet::new() ;
    types.insert( cst.get().typ() ) ;
    let term = factory.cst(cst) ;
    TermAndDep {
      term: term,
      apps: HashSet::new(),
      vars: HashSet::new(),
      types: types,
      linear: true,
      qf: true,
      span: span,
    }
  }

  /// Merges some terms with dependencies.
  #[inline(always)]
  fn merge(kids: Vec<TermAndDep>) -> (
    Vec<Term>,
    HashSet<Sym>,
    HashSet<Var>,
    HashSet<Type>,
    usize,
    bool,
    bool,
  ) {
    use std::iter::Extend ;
    let mut subs = vec![] ;
    let mut apps = HashSet::new() ;
    let mut vars = HashSet::new() ;
    let mut types = HashSet::new() ;
    let mut linear = true ;
    let mut qf = true ;
    let mut kids_with_vars = 0 ;
    for kid in kids.into_iter() {
      subs.push( kid.term ) ;
      apps.extend( kid.apps ) ;
      if ! kid.vars.is_empty() {
        kids_with_vars = kids_with_vars + 1
      } ;
      vars.extend( kid.vars ) ;
      types.extend( kid.types ) ;
      if ! kid.linear { linear = false } ;
      if ! kid.qf { qf = false } ;
    }
    ( subs, apps, vars, types, kids_with_vars, linear, qf )
  }

  /// Parses an operator.
  pub fn op(
    factory: & Factory, op: Operator, kids: Vec<TermAndDep>, span: Spn
  ) -> Self {
    use term::Operator::* ;
    use term::OpMaker ;
    let (
      subs, apps, vars, types, kids_with_vars, linear, qf
    ) = Self::merge(kids) ;
    let linear = linear && match op {
      Mul | Div => kids_with_vars >= 2,
      _ => false,
    } ;
    let term = factory.op(op, subs) ;
    TermAndDep {
      term: term,
      apps: apps,
      vars: vars,
      types: types,
      linear: linear,
      qf: qf,
      span: span,
    }
  }

  /// Parses an application.
  pub fn app(
    factory: & Factory, sym: Sym, kids: Vec<TermAndDep>, span: Spn
  ) -> Self {
    use term::AppMaker ;
    let (
      subs, mut apps, vars, types, kids_with_vars, linear, qf
    ) = Self::merge(kids) ;
    let linear = linear && kids_with_vars >= 2 ;
    apps.insert(sym.clone()) ;
    let term = factory.app(sym, subs) ;
    TermAndDep {
      term: term,
      apps: apps,
      vars: vars,
      types: types,
      linear: linear,
      qf: qf,
      span: span,
    }
  }

  /// Parses a quantifier.
  fn quantifier(
    factory: & Factory, bindings: Vec<(Sym, Spnd<Type>)>, kid: TermAndDep,
    univ: bool, span: Spn
  ) -> Self {
    use term::BindMaker ;
    let term = kid.term ;
    let apps = kid.apps ;
    let mut vars = kid.vars ;
    let mut types = kid.types ;
    let linear = kid.linear ;
    let mut binds = vec![] ;
    for (sym, typ) in bindings.into_iter() {
      let var = factory.var(sym.clone()) ;
      let was_there = vars.remove(& var) ;
      if was_there {
        binds.push( (sym, * typ) ) ;
        types.insert(* typ) ;
        ()
      } ;
    } ;
    let term = if univ {
      factory.forall(binds, term)
    } else {
      factory.exists(binds, term)
    } ;
    TermAndDep {
      term: term,
      apps: apps,
      vars: vars,
      types: types,
      linear: linear,
      qf: true,
      span: span,
    }
  }

  /// Parses a universal quantifier.
  pub fn forall(
    factory: & Factory, bindings: Vec<(Sym, Spnd<Type>)>, kid: TermAndDep,
    span: Spn
  ) -> Self {
    Self::quantifier(factory, bindings, kid, true, span)
  }

  /// Parses an existential quantifier.
  pub fn exists(
    factory: & Factory, bindings: Vec<(Sym, Spnd<Type>)>, kid: TermAndDep,
    span: Spn
  ) -> Self {
    Self::quantifier(factory, bindings, kid, true, span)
  }

  /// Parses a let binding.
  pub fn let_b(
    factory: & Factory, bindings: Vec<(Sym, TermAndDep)>, kid: TermAndDep,
    span: Spn
  ) -> Self {
    use term::BindMaker ;
    use std::iter::Extend ;
    let term = kid.term ;
    let mut apps = kid.apps ;
    let mut vars = kid.vars ;
    let mut types = kid.types ;
    let mut linear = kid.linear ;
    let mut qf = kid.qf ;
    let mut binds = vec![] ;
    let mut bind_vars = HashSet::new() ;
    for (sym, res) in bindings.into_iter() {
      let var = factory.var(sym.clone()) ;
      let was_there = vars.remove(& var) ;
      if was_there {
        let term = res.term ;
        apps.extend(res.apps) ;
        bind_vars.extend(res.vars) ;
        types.extend(res.types) ;
        linear = linear && res.linear ;
        qf = qf && res.qf ;
        binds.push( (sym, term) ) ;
      } else {
      }
    } ;
    vars.extend(bind_vars) ;
    let term = factory.let_b(binds, term) ;
    TermAndDep {
      term: term,
      apps: apps,
      vars: vars,
      types: types,
      linear: linear,
      qf: qf,
      span: span,
    }
  }
}

mk_parser!{
  #[doc = "State parser."]
  pub fn state(bytes, offset: usize) -> Spnd<State> {
    let mut len = 0 ;
    do_parse!(
      bytes,
      len_set!(len < char '_') >>
      len_add!(len < spc cmt) >>
      state: alt!(
        map!(
          len_add!(len < tag "curr"),
          |_| Spnd::len_mk(
            State::Curr, offset, len
          )
        ) |
        map!(
          len_add!(len < tag "next"),
          |_| Spnd::len_mk(
            State::Next, offset, len
          )
         )
      ) >> (state)
    )
  }
}

mk_parser!{
  #[doc = "Parsed a spanned ident."]
  pub fn id_parser(bytes, offset: usize) -> Spnd<String> {
    let mut len = 0 ;
    alt!(
      bytes,
      // Simple symbol.
      do_parse!(
        head: map!(
          simple_symbol_head, |c| { len = 1 ; c }
        ) >>
        tail: opt!(
          map_res!(
            simple_symbol_tail, str::from_utf8
          )
        ) >> ({
          let id = format!("{}{}", head, tail.unwrap_or("")) ;
          len = id.len() ;
          Spnd::len_mk(id, offset, len)
        })
      ) |
      // Quoted symbol.
      //
      // Careful with the handling of `len` here, don't fuck it up if you touch
      // this.
      delimited!(
        char!('|'),
        do_parse!(
          head: none_of!("|\\@") >>
          tail: map_res!(is_not!("|\\"), str::from_utf8) >> ({
            let id = format!("{}{}", head, tail) ;
            len = id.len() + 2 ;
            Spnd::len_mk(id, offset, len)
          })
        ),
        char!('|')
      )
    )
  }
}

/// Parsed a spanned symbol.
pub fn sym_parser<'a>(
  bytes: Bytes<'a>, offset: usize, f: & Factory
) -> IResult<& 'a [u8], Spnd<Sym>> {
  use sym::SymMaker ;
  map!(
    bytes,
    apply!(id_parser, offset),
    |s: Spnd<String>| s.map( |s| f.sym(s) )
  )
}

/// Spanned variable parser.
pub fn var_parser<'a>(
  bytes: & 'a [u8], offset: usize, f: & Factory
) -> IResult<& 'a [u8], TermAndDep> {
  use sym::SymMaker ;
  use var::VarMaker ;
  let mut len = 0 ;
  alt!(
    bytes,
    do_parse!(
      len_set!(len < char '(') >>
      len_add!(len < opt spc cmt) >>
      state: len_add!(len < spn apply!(state, offset + len)) >>
      len_add!(len < spc cmt) >>
      sym: map!(
        len_add!(len < spn apply!(id_parser, offset + len)),
        |s| f.sym(s)
      ) >>
      len_add!(len < opt spc cmt) >>
      len_add!(len < char ')') >> ({
        let var = f.svar(sym, state) ;
        TermAndDep::var(f, var, Spn::len_mk(offset, len))
      })
    ) |
    map!(
      apply!(id_parser, offset), |sym| {
        let (sym, span) = Spnd::destroy(sym) ;
        let var = f.var( f.sym(sym) ) ;
        TermAndDep::var(f, var, span)
      }
    )
  )
}

/// Spanned constant parser.
pub fn cst_parser<'a>(
  bytes: & 'a [u8], offset: usize, f: & Factory
) -> IResult<& 'a [u8], TermAndDep> {
  map!(
    bytes,
    apply!( super::cst_parser, offset, f ),
    |cst: Spnd<Cst>| {
      let (cst, span) = cst.destroy() ;
      TermAndDep::cst(f, cst, span)
    }
  )
}

/// Spanned operator parser.
pub fn op_parser<'a>(
  bytes: & 'a [u8], offset: usize, f: & Factory
) -> IResult<& 'a [u8], TermAndDep> {
  let mut len = 0 ;
  do_parse!(
    bytes,
    len_set!(len < char '(') >>
    len_add!(len < opt spc cmt) >>
    op: len_add!(
      len < spn apply!(operator_parser, offset + len)
    ) >>
    len_add!(len < spc cmt) >>
    args: many1!(
      do_parse!(
        term: len_add!(
          len < trm apply!(term_parser, offset + len, f)
        ) >>
        len_add!(len < spc cmt) >> (term)
      )
    ) >>
    len_add!(len < opt spc cmt) >>
    len_add!(len < char ')') >>(
      TermAndDep::op(f, op, args, Spn::len_mk(offset, len))
    )
  )
}

/// Spanned quantifier parser.
pub fn quantified_parser<'a>(
  bytes: & 'a [u8], offset: usize, f: & Factory
) -> IResult<& 'a [u8], TermAndDep> {
  use sym::SymMaker ;
  let mut len = 0 ;
  do_parse!(
    bytes,
    len_set!(len < char '(') >>
    len_add!(len < opt spc cmt) >>
    quantifier: len_add!(
      len < spn apply!(quantifier_parser, offset + len)
    ) >>
    len_add!(len < opt spc cmt) >>
    len_add!(len < char '(') >>
    bindings: separated_list!(
      len_add!(len < spc cmt),
      delimited!(
        len_add!(len < char '('),
        do_parse!(
          len_add!(len < opt spc cmt) >>
          sym: map!(
            len_add!(len < spn apply!(id_parser, offset + len)),
            |sym| f.sym(sym)
          ) >>
          len_add!(len < spc cmt) >>
          ty: map!(
            apply!(type_parser, offset + len),
            |ty: Spnd<Type>| { len += ty.len() ; ty }
          ) >>
          len_add!(len < opt spc cmt) >> (sym, ty)
        ),
        len_add!(len < char ')')
      )
    ) >>
    len_add!(len < opt spc cmt) >>
    len_add!(len < char ')') >>
    len_add!(len < opt spc cmt) >>
    term: len_add!(len < trm apply!(term_parser, offset + len, f)) >>
    len_add!(len < opt spc cmt) >>
    len_add!(len < char ')') >> (
      match quantifier {
        Quantifier::Forall => TermAndDep::forall(
          f, bindings, term, Spn::len_mk(offset, len)
        ),
        Quantifier::Exists => TermAndDep::exists(
          f, bindings, term, Spn::len_mk(offset, len)
        ),
      }
    )
  )
}

/// Spanned let binding parser.
pub fn let_parser<'a>(
  bytes: & 'a [u8], offset: usize, f: & Factory
) -> IResult<& 'a [u8], TermAndDep> {
  use sym::SymMaker ;
  let mut len = 0 ;
  do_parse!(
    bytes,
    len_set!(len < char '(') >>
    len_add!(len < opt spc cmt) >>
    len_add!(len < tag "let") >>
    len_add!(len < opt spc cmt) >>
    len_add!(len < char'(') >>
    len_add!(len < opt spc cmt) >>
    bindings: separated_list!(
      len_add!(len < spc cmt),
      delimited!(
        len_add!(len < char '('),
        do_parse!(
          len_add!(len < spc cmt) >>
          sym: map!(
            len_add!(len < spn apply!(id_parser, offset + len)),
            |sym| f.sym(sym)
          ) >>
          len_add!(len < spc cmt) >>
          term: len_add!(
            len < trm apply!(term_parser, offset + len, f)
          ) >> (
            sym, term
          )
        ),
        len_add!(len < char ')')
      )
    ) >>
    len_add!(len < opt spc cmt) >>
    len_add!(len < char ')') >>
    len_add!(len < opt spc cmt) >>
    term: len_add!(len < trm apply!(term_parser, offset + len, f)) >>
    len_add!(len < opt spc cmt) >>
    len_add!(len < char ')') >> (
      TermAndDep::let_b(f, bindings, term, Spn::len_mk(offset,len))
    )
  )
}

/// Spanned application parser.
fn app_parser<'a>(
  bytes: & 'a [u8], offset: usize, f: & Factory
) -> IResult<& 'a [u8], TermAndDep> {
  use sym::SymMaker ;
  let mut len = 0 ;
  do_parse!(
    bytes,
    len_set!(len < char '(') >>
    len_add!(len < spc cmt) >>
    sym: map!(
      len_add!(len < spn apply!(id_parser, offset + len)),
      |sym| f.sym(sym)
    ) >>
    len_add!(len < spc cmt) >>
    args: separated_nonempty_list!(
      len_add!(len < spc cmt),
      len_add!(len < trm apply!(term_parser, offset + len, f))
    ) >>
    len_add!(len < opt spc cmt) >>
    len_add!(len < char ')') >> ({
      TermAndDep::app(f, sym, args, Spn::len_mk(offset, len))
    })
  )
}

/// VMT spanned term parser.
pub fn term_parser<'a>(
  bytes: & 'a [u8], offset: usize, f: & Factory
) -> IResult<& 'a [u8], TermAndDep> {
  let mut len = 0 ;
  alt!(
    bytes,
    apply!(cst_parser, offset, f) |
    apply!(var_parser, offset, f) |
    apply!(op_parser, offset, f) |
    apply!(quantified_parser, offset, f) |
    apply!(let_parser, offset, f) |
    apply!(app_parser, offset, f) |
    do_parse!(
      len_set!(len < char '(') >>
      len_add!(len < opt spc cmt) >>
      t: len_add!(
        len < trm apply!(term_parser, offset + len, f)
      ) >>
      len_add!(len < opt spc cmt) >>
      len_add!(len < char ')') >> ({
        let mut t = t ;
        t.span = Spn::len_mk(offset, len) ;
        t
      })
    )
  )
}




mk_parser!{
  #[doc = "
    Parses a token, used for error reporting.
    Returns the token's span and a description of the token.

    Always succeeds.
  "]
  pub fn token_parser(bytes, offset: usize) -> (Spn, String) {
    alt_complete!(
      bytes,
      map!(
        apply!(super::rat_parser, offset), |res| (
          Spnd::to_span(res), "a rational".into()
        )
      ) |
      map!(
        apply!(super::int_parser, offset), |res| (
          Spnd::to_span(res), "an integer".into()
        )
      ) |
      map!(
        apply!(super::bool_parser, offset), |res| (
          Spnd::to_span(res), "a boolean".into()
        )
      ) |
      map!(
        apply!(type_parser, offset), |res| (
          Spnd::to_span(res), "a type".into()
        )
      ) |
      map!(
        apply!(id_parser, offset), |res| (
          Spnd::to_span(res), "an identifier".into()
        )
      ) |
      map!(
        take_str!(1), |res: & str| (
          Spn::len_mk(offset, 1), format!("`{}`", res)
        )
      ) |
      map!(
        take!(0), |_| (
          Spn::len_mk(offset, 1), "end of file".into()
        )
      )
    )
  }
}

#[test]
fn test_token_parser() {
  try_parse!{
    |bytes| token_parser(bytes, 7), b"blah", (s, res) -> {
      assert_eq!(res, (Spn::len_mk(7, 4), "an identifier".into()))
    }
  }
  try_parse!{
    |bytes| token_parser(bytes, 7), b"7.32", (s, res) -> {
      assert_eq!(res, (Spn::len_mk(7, 4), "a rational".into()))
    }
  }
  try_parse!{
    |bytes| token_parser(bytes, 7), b"732", (s, res) -> {
      assert_eq!(res, (Spn::len_mk(7, 3), "an integer".into()))
    }
  }
  try_parse!{
    |bytes| token_parser(bytes, 7), b"false)", (s, res) -> {
      assert_eq!(res, (Spn::len_mk(7, 5), "a boolean".into()))
    }
  }
  try_parse!{
    |bytes| token_parser(bytes, 7), b")", (s, res) -> {
      assert_eq!(res, (Spn::len_mk(7, 1), "`)`".into()))
    }
  }
  try_parse!{
    |bytes| token_parser(bytes, 7), b"", (s, res) -> {
      assert_eq!(res, (Spn::len_mk(7, 1), "end of file".into()))
    }
  }
}



#[cfg(test)]
macro_rules! try_parse_term {
  ($fun:expr, $factory:expr, $arg:expr, $e:expr) => (
    try_parse!($fun, $factory, $arg,
      (s, res) -> {
        assert_eq!(res.term, * $e) ;
        assert_eq!(res.span, $e.span)
      }
    )
  ) ;
}


#[cfg(test)]
mod terms {
  use base::{ PrintVmt } ;
  use sym::* ;
  use term::{ CstMaker, OpMaker, AppMaker } ;
  use factory::* ;
  use typ::* ;
  use std::str::FromStr ;

  #[test]
  fn cst() {
    use super::* ;
    let factory = Factory::mk() ;
    let res: Term = factory.cst( Int::from_str("7").unwrap() ) ;
    try_parse_term!(
      |bytes, factory| term_parser(bytes, 3, factory), & factory, b"7",
      Spnd::len_mk(res.clone(), 3, 1)
    ) ;
    let res: Term = factory.cst(
      Rat::new(
        Int::from_str("5357").unwrap(),
        Int::from_str("2046").unwrap()
      )
    ) ;
    try_parse_term!(
      |bytes, factory| term_parser(bytes, 3, factory), & factory,
      b"(/ 5357 2046)",
      Spnd::len_mk(res.clone(), 3, 13)
    ) ;
    let res: Term = factory.cst(
      Rat::new(
        Int::from_str("0").unwrap(),
        Int::from_str("1").unwrap()
      )
    ) ;
    try_parse_term!(
      |bytes, factory| term_parser(bytes, 3, factory), & factory,
      b"0.0",
      Spnd::len_mk(res.clone(), 3, 3)
    ) ;
    let res: Term = factory.cst( true ) ;
    try_parse_term!(
      |bytes, factory| term_parser(bytes, 3, factory), & factory, b"true",
      Spnd::len_mk(res.clone(), 3, 4)
    ) ;
    let res: Term = factory.cst( false ) ;
    try_parse_term!(
      |bytes, factory| term_parser(bytes, 3, factory), & factory, b"false",
      Spnd::len_mk(res.clone(), 3, 5)
    ) ;
  }

  #[test]
  fn var() {
    use super::* ;
    let factory = Factory::mk() ;
    let res: Term = factory.var( factory.sym("bla") ) ;
    try_parse_term!(
      |bytes, factory| term_parser(bytes, 9, factory), & factory, b"|bla|",
      Spnd::len_mk(res.clone(), 9, 5)
    ) ;
    let res: Term = factory.var( factory.sym("bly.bla") ) ;
    try_parse_term!(
      |bytes, factory| term_parser(bytes, 9, factory), & factory, b"|bly.bla|",
      Spnd::len_mk(res.clone(), 9, 9)
    ) ;
    let res: Term = factory.svar( factory.sym("bla"), State::Curr ) ;
    try_parse_term!(
      |bytes, factory| term_parser(bytes, 9, factory), & factory,
      b"(_ curr |bla|)",
      Spnd::len_mk(res.clone(), 9, 14)
    ) ;
    let res: Term = factory.svar( factory.sym("bla"), State::Next ) ;
    try_parse_term!(
      |bytes, factory| term_parser(bytes, 9, factory), & factory,
      b"(_ next |bla|)",
      Spnd::len_mk(res.clone(), 9, 14)
    ) ;
  }

  #[test]
  fn op() {
    use super::* ;
    let factory = Factory::mk() ;

    let bla_plus_7: Term = factory.op(
      Operator::Add, vec![
        factory.var( factory.sym("bla") ),
        factory.cst( Int::from_str("7").unwrap() )
      ]
    ) ;
    let mut s: Vec<u8> = vec![] ;
    bla_plus_7.to_vmt(& mut s).unwrap() ;
    try_parse_term!(
      |bytes, factory| term_parser(bytes, 9, factory), & factory, & s,
      Spnd::len_mk(bla_plus_7.clone(), 9, s.len())
    ) ;

    let nested: Term = factory.op(
      Operator::Le, vec![
        factory.cst( Int::from_str("17").unwrap() ), bla_plus_7
      ]
    ) ;
    let mut s: Vec<u8> = vec![] ;
    nested.to_vmt(& mut s).unwrap() ;
    try_parse_term!(
      |bytes, factory| term_parser(bytes, 9, factory), & factory, & s,
      Spnd::len_mk(nested.clone(), 9, s.len())
    ) ;

    let nested: Term = factory.op(
      Operator::And, vec![
        factory.svar( factory.sym("svar"), State::Curr ),
        nested
      ]
    ) ;
    let mut s: Vec<u8> = vec![] ;
    nested.to_vmt(& mut s).unwrap() ;
    try_parse_term!(
      |bytes, factory| term_parser(bytes, 9, factory), & factory, & s,
      Spnd::len_mk(nested.clone(), 9, s.len())
    ) ;

    let nested: Term = factory.op(
      Operator::Or, vec![
        factory.svar( factory.sym("something else"), State::Next ),
        nested
      ]
    ) ;
    let mut s: Vec<u8> = vec![] ;
    nested.to_vmt(& mut s).unwrap() ;
    try_parse_term!(
      |bytes, factory| term_parser(bytes, 9, factory), & factory, & s,
      Spnd::len_mk(nested.clone(), 9, s.len())
    ) ;

    let nested: Term = factory.op(
      Operator::Ite, vec![
        factory.var( factory.sym("bla.bla") ),
        factory.op(
          Operator::Eq, vec![
            factory.var( factory.sym("bli.blu") ),
            factory.cst( Int::from_str("1").unwrap() )
          ]
        ),
        factory.op(
          Operator::Eq, vec![
            factory.var( factory.sym("bli.blu") ),
            factory.cst( Int::from_str("0").unwrap() )
          ]
        ),
      ]
    ) ;
    let mut s: Vec<u8> = vec![] ;
    nested.to_vmt(& mut s).unwrap() ;
    try_parse_term!(
      |bytes, factory| term_parser(bytes, 9, factory), & factory, & s,
      Spnd::len_mk(nested.clone(), 9, s.len())
    ) ;
  }

  #[test]
  fn app() {
    use super::* ;
    let factory = Factory::mk() ;

    let bla_plus_7: Term = factory.app(
      factory.sym("function symbol"), vec![
        factory.var( factory.sym("bla") ),
        factory.cst( Int::from_str("7").unwrap() )
      ]
    ) ;
    let mut s: Vec<u8> = vec![] ;
    bla_plus_7.to_vmt(& mut s).unwrap() ;
    try_parse_term!(
      |bytes, factory| term_parser(bytes, 9, factory), & factory, & s,
      Spnd::len_mk(bla_plus_7.clone(), 9, s.len())
    ) ;

    let nested: Term = factory.app(
      factory.sym("another function symbol"), vec![
        factory.cst( Int::from_str("17").unwrap() ),
        bla_plus_7
      ]
    ) ;
    let mut s: Vec<u8> = vec![] ;
    nested.to_vmt(& mut s).unwrap() ;
    try_parse_term!(
      |bytes, factory| term_parser(bytes, 9, factory), & factory, & s,
      Spnd::len_mk(nested.clone(), 9, s.len())
    ) ;

    let nested: Term = factory.app(
      factory.sym("yet another one"), vec![
        factory.svar( factory.sym("svar"), State::Curr ),
        nested
      ]
    ) ;
    let mut s: Vec<u8> = vec![] ;
    nested.to_vmt(& mut s).unwrap() ;
    try_parse_term!(
      |bytes, factory| term_parser(bytes, 9, factory), & factory, & s,
      Spnd::len_mk(nested.clone(), 9, s.len())
    ) ;

    let nested: Term = factory.op(
      Operator::Or, vec![
        factory.svar( factory.sym("something else"), State::Next ),
        nested
      ]
    ) ;
    let mut s: Vec<u8> = vec![] ;
    nested.to_vmt(& mut s).unwrap() ;
    try_parse_term!(
      |bytes, factory| term_parser(bytes, 9, factory), & factory, & s,
      Spnd::len_mk(nested.clone(), 9, s.len())
    ) ;
  }

  #[test]
  fn empty() {
    let factory = Factory::mk() ;
    match super::term_parser(& b""[..], 0, & factory) {
      ::nom::IResult::Incomplete(_) => (),
      other => panic!("unexpected result on parsing empty string: {:?}", other)
    } ;
    ()
  }
}

