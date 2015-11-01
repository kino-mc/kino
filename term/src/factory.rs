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

use base::{ Mkable, State, Offset, Smt2Offset } ;
use typ::{ Type, Bool, Int, Rat } ;
use sym::{ SymConsign, Sym, SymMaker } ;
use cst::{ Cst, CstConsign } ;
use term::{
  TermConsign, Operator, Term,
  CstMaker, VarMaker, OpMaker, AppMaker, BindMaker, UnTermOps
} ;
use parser ;

macro_rules! try_parse {
  ($fun:expr, $arg: expr, $res:pat => $b:block) => (
    match $fun($arg) {
      ::nom::IResult::Done(i,$res) => {
        let res = $b ;
        ::nom::IResult::Done(i, res)
      },
      ::nom::IResult::Error(e) => ::nom::IResult::Error(e),
      ::nom::IResult::Incomplete(n) => ::nom::IResult::Incomplete(n),
    }
  ) ;
}

/** Factory for terms. */
#[derive(Clone)]
pub struct Factory {
  /** Hash cons table for constants. */
  cst: CstConsign,
  /** Hash cons table for function symbols. */
  sym: SymConsign,
  /** Hash cons table for terms. */
  term: TermConsign,
}

impl Factory {
  /** Creates an empty term factory. */
  pub fn mk() -> Self {
    Factory {
      cst: CstConsign::mk(), sym: SymConsign::mk(), term: TermConsign::mk()
    }
  }
  /** The hash cons table for constants. */
  pub fn cst_consign(& self) -> & CstConsign {
    & self.cst
  }
}

impl CstMaker<Cst> for Factory {
  fn cst(& self, cst: Cst) -> Term {
    self.term.cst(cst)
  }
}
impl CstMaker<Bool> for Factory {
  fn cst(& self, cst: Bool) -> Term {
    use cst::ConstMaker ;
    self.term.cst( self.cst.constant(cst) )
  }
}
impl CstMaker<Int> for Factory {
  fn cst(& self, cst: Int) -> Term {
    use cst::ConstMaker ;
    self.term.cst( self.cst.constant(cst) )
  }
}
impl CstMaker<Rat> for Factory {
  fn cst(& self, cst: Rat) -> Term {
    use cst::ConstMaker ;
    self.term.cst( self.cst.constant(cst) )
  }
}

impl<'a> SymMaker<& 'a str> for Factory {
  fn sym(& self, sym: & 'a str) -> Sym {
    self.sym.sym(sym)
  }
}
impl SymMaker<String> for Factory {
  fn sym(& self, sym: String) -> Sym {
    self.sym.sym(sym)
  }
}

impl VarMaker<String> for Factory {
  fn var(& self, sym: String) -> Term {
    self.term.var( self.sym(sym) )
  }
  fn svar(& self, sym: String, st: State) -> Term {
    self.term.svar( self.sym(sym), st )
  }
}

impl<'a> VarMaker<& 'a str> for Factory {
  fn var(& self, sym: & 'a str) -> Term {
    self.term.var( self.sym(sym) )
  }
  fn svar(& self, sym: & 'a str, st: State) -> Term {
    self.term.svar( self.sym(sym), st )
  }
}

impl VarMaker<Sym> for Factory {
  fn var(& self, sym: Sym) -> Term { self.term.var(sym) }
  fn svar(& self, sym: Sym, st: State) -> Term { self.term.svar(sym,st) }
}

impl OpMaker for Factory {
  fn op(& self, op: Operator, args: Vec<Term>) -> Term {
    self.term.op(op, args)
  }
}

impl AppMaker<Sym> for Factory {
  fn app(& self, sym: Sym, args: Vec<Term>) -> Term {
    self.term.app(sym, args)
  }
}

impl BindMaker<Term> for Factory {
  fn forall(
    & self, bindings: Vec<(Sym, Type)>, term: Term
  ) -> Term {
    self.term.forall(bindings, term)
  }
  fn exists(
    & self, bindings: Vec<(Sym, Type)>, term: Term
  ) -> Term {
    self.term.exists(bindings, term)
  }
  fn let_b(
    & self, bindings: Vec<(Sym, Term)>, term: Term
  ) -> Term {
    self.term.let_b(bindings, term)
  }
}

impl UnTermOps<Term> for Factory {
  fn bump(& self, term: Term) -> Result<Term,()> { self.term.bump(term) }
}







impl ParseSmt2 for Factory {
  type Ident = (Sym, Option<Offset>) ;
  type Value = Cst ;
  type Expr = (Term, Smt2Offset) ;
  type Proof = () ;
  fn parse_ident<'a>(
    & self, bytes: & 'a [u8]
  ) -> IResult<'a, & 'a [u8], (Sym, Option<Offset>)> {
    map!(
      bytes,
      parser::smt2::id_parser,
      |(sym, offset)| match offset {
        Smt2Offset::No => (self.sym(sym), None),
        Smt2Offset::One(o) => (self.sym(sym), Some(o)),
        _ => unreachable!(),
      }
    )
  }
  fn parse_value<'a>(
    & self, bytes: & 'a [u8]
  ) -> IResult<'a, & 'a [u8], Cst> {
    parser::cst_parser(bytes, & self.cst)
  }
  fn parse_expr<'a>(
    & self, bytes: & 'a [u8]
  ) -> IResult<'a, & 'a [u8], (Term, Smt2Offset)> {
    parser::smt2::term_parser(bytes, self)
  }
  fn parse_proof<'a>(
    & self, bytes: & 'a [u8]
  ) -> IResult<'a, & 'a [u8], ()> {
    unimpl!()
  }
}


/** Parsers for SMT Lib 2 Transition Systems */
pub trait ParseSts2 {
  /** Type of identifiers when parsing an STS system. */
  type Ident ;
  /** Type of expressions when parsing an STS system. */
  type Expr ;
  /** Type of types when parsing an STS system. */
  type Type ;
  /** Parses an identifier in STS format. */
  fn parse_ident<'a>(
    & self, bytes: & 'a [u8]
  ) -> IResult<'a, & 'a [u8], Self::Ident> ;
  /** Parses an expression in STS format. */
  fn parse_expr<'a>(
    & self, bytes: & 'a [u8]
  ) -> IResult<'a, & 'a [u8], Self::Expr> ;
  /** Parses a Type in STS format. */
  fn parse_type<'a>(
    & self, bytes: & 'a [u8]
  ) -> IResult<'a, & 'a [u8], Self::Type> ;
}

impl ParseSts2 for Factory {
  type Ident = Sym ;
  type Expr = Term ;
  type Type = Type ;
  fn parse_ident<'a>(
    & self, bytes: & 'a [u8]
  ) -> IResult<'a, & 'a [u8], Sym> {
    map!(
      bytes,
      parser::sts2::id_parser,
      |sym| self.sym(sym)
    )
  }
  fn parse_expr<'a>(
    & self, bytes: & 'a [u8]
  ) -> IResult<'a, & 'a [u8], Term> {
    parser::sts2::term_parser(bytes, self)
  }
  fn parse_type<'a>(
    & self, bytes: & 'a [u8]
  ) -> IResult<'a, & 'a [u8], Type> {
    parser::type_parser(bytes)
  }
}
