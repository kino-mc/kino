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
use var::{ Var, VarConsign, VarMaker } ;
use term::{
  TermConsign, Operator, Term,
  CstMaker, VariableMaker, OpMaker, AppMaker, BindMaker,
  bump
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
  /** Hash cons table for function symbols. */
  sym: SymConsign,
  /** Hash cons table for variabls. */
  var: VarConsign,
  /** Hash cons table for constants. */
  cst: CstConsign,
  /** Hash cons table for terms. */
  term: TermConsign,
}

impl Factory {
  /** Creates an empty term factory. */
  pub fn mk() -> Self {
    Factory {
      sym: SymConsign::mk(),
      var: VarConsign::mk(),
      cst: CstConsign::mk(),
      term: TermConsign::mk(),
    }
  }
  /** Parses a type. */
  pub fn parse_type<'a>(bytes: & 'a [u8]) -> IResult<'a, & 'a [u8], Type> {
    parser::type_parser(bytes)
  }
  /** The hash cons table for constants. */
  pub fn cst_consign(& self) -> & CstConsign {
    & self.cst
  }
}


/* |===| Factory can create symbols. */

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


/* |===| Factory can create constants. */

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


/* |===| Factory can create variables. */

impl VarMaker<String, Term> for Factory {
  fn var(& self, sym: String) -> Term {
    self.term.var(
      self.var.var( self.sym(sym) )
    )
  }
  fn svar(& self, sym: String, st: State) -> Term {
    self.term.var(
      self.var.svar( self.sym(sym), st )
    )
  }
}
impl<'a> VarMaker<& 'a str, Term> for Factory {
  fn var(& self, sym: & 'a str) -> Term {
    self.term.var(
      self.var.var( self.sym(sym) )
    )
  }
  fn svar(& self, sym: & 'a str, st: State) -> Term {
    self.term.var(
      self.var.svar( self.sym(sym), st )
    )
  }
}
impl VarMaker<Sym, Term> for Factory {
  fn var(& self, sym: Sym) -> Term {
    self.term.var(
      self.var.var(sym)
    )
  }
  fn svar(& self, sym: Sym, st: State) -> Term {
    self.term.var(
      self.var.svar(sym,st)
    )
  }
}


/* |===| Factory can create operator applications. */

impl OpMaker for Factory {
  fn op(& self, op: Operator, args: Vec<Term>) -> Term {
    self.term.op(op, args)
  }
}


/* |===| Factory can create function symbol applications. */

impl AppMaker<Sym> for Factory {
  fn app(& self, sym: Sym, args: Vec<Term>) -> Term {
    self.term.app(sym, args)
  }
}


/* |===| Factory can create quantifier and let-bindings. */

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


/* |===| Factory is a term factory. */

impl ::term::Factory for Factory {}


/* |===| Factory can perform unary operations on terms. */

/** Unary operations on terms. */
pub trait UnTermOps<Trm> {
  /** Bumps a term.

  * changes all `SVar(sym, State::curr)` to `SVar(sym, State::next)`,
  * returns `Err(())` if input term contains a `SVar(_, State::next)`. */
  fn bump(& self, Trm) -> Result<Term,()> ;
}
impl<
  'a, Trm: Clone, T: UnTermOps<Trm> + Sized
> UnTermOps<& 'a Trm> for T {
  #[inline(always)]
  fn bump(& self, term: & 'a Trm) -> Result<Term,()> {
    (self as & UnTermOps<Trm>).bump(term.clone())
  }
}

impl UnTermOps<Term> for Factory {
  fn bump(& self, term: Term) -> Result<Term,()> { bump(self, term) }
}







impl ParseSmt2 for Factory {
  type Ident = (Var, Option<Offset>) ;
  type Value = Cst ;
  type Expr = (Term, Smt2Offset) ;
  type Proof = () ;
  fn parse_ident<'a>(
    & self, bytes: & 'a [u8]
  ) -> IResult<'a, & 'a [u8], (Var, Option<Offset>)> {
    map!(
      bytes,
      parser::smt2::id_parser,
      |(sym, offset)| match offset {
        Smt2Offset::No => (
          self.var.var(self.sym(sym)), None
        ),
        Smt2Offset::One(o) => (
          self.var.svar( self.sym(sym), State::Curr ), Some(o)
        ),
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
    & self, _: & 'a [u8]
  ) -> IResult<'a, & 'a [u8], ()> {
    unimpl!()
  }
}


/** Parsers for STS Systems */
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
