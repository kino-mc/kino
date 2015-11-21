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

use rsmt2::ParseSmt2 ;

use base::{ Mkable, State, Offset, Offset2, Smt2Offset } ;
use typ::{ Type, Bool, Int, Rat } ;
use sym::{ SymConsign, Sym, SymMaker } ;
use cst::{ RealCst, Cst, CstConsign } ;
use var::{ Var, VarConsign, VarMaker } ;
use term::{
  TermConsign, Operator, Term, RealTerm,
  CstMaker, VariableMaker, OpMaker, AppMaker, BindMaker,
  bump
} ;
use parser ;
use parser::tsv::TermAndDep ;

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

// /** Helper macro to create operators. */
// macro_rules! op_maker {
//   ($doc:expr, fn $name:ident(1) for $op:ident) => (
//     #[doc=$doc]
//     pub fn $name(& self, kid: Term) -> Term {
//       self.op(Operator::$op, vec![ kid ])
//     }
//   ) ;
//   ($doc:expr, fn $name:ident(2) for $op:ident) => (
//     #[doc=$doc]
//     pub fn $name(& self, lhs: Term, rhs: Term) -> Term {
//       self.op(Operator::$op, vec![ lhs, rhs ])
//     }
//   ) ;
//   ($doc:expr, fn $name:ident(3) for $op:ident) => (
//     #[doc=$doc]
//     pub fn $name(& self, wan: Term, two: Term, tri: Term) -> Term {
//       self.op(Operator::$op, vec![ wan, two, tri ])
//     }
//   ) ;
//   ($doc:expr, fn $name:ident(*) for $op:ident) => (
//     #[doc=$doc]
//     pub fn $name(& self, kids: Vec<Term>) -> Term {
//       self.op(Operator::$op, kids)
//     }
//   ) ;
// }

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

  /** Creates a variable from a `Var`. */
  pub fn mk_var(& self, var: Var) -> Term {
    self.term.var(var)
  }

  /** Creates a constant from a `Cst`. */
  pub fn mk_cst(& self, cst: Cst) -> Term {
    self.term.cst(cst)
  }

  /** Creates a constant from a real `Cst`. */
  pub fn mk_rcst(& self, cst: ::real_term::Cst) -> Cst {
    use cst::ConstMaker ;
    self.cst.constant(cst)
  }



  /** Creates an n-ary equality. */
  pub fn eq(& self, kids: Vec<Term>) -> Term {
    debug_assert!(kids.len() > 1) ;
    self.op(Operator::Eq, kids)
  }

  /** Creates an if-then-else. */
  pub fn ite(& self, condition: Term, then: Term, els3: Term) -> Term {
    if then == els3 {
      return then
    } else {
      match * condition.get() {
        RealTerm::C( ref c ) => match * c.get() {
          RealCst::Bool(true) => return then,
          RealCst::Bool(false) => return els3,
          _ => (),
        },
        _ => (),
      }
    } ;
    self.op(Operator::Ite, vec![ condition, then, els3 ])
  }

  /** Creates a negation. */
  pub fn not(& self, term: Term) -> Term {
    match * term.get() {
      RealTerm::C( ref c ) => match * c.get() {
        RealCst::Bool(true) => return self.cst(false),
        RealCst::Bool(false) => return self.cst(true),
        _ => (),
      },
      RealTerm::Op(Operator::Not, ref kids) => {
        debug_assert!(kids.len() == 1) ;
        return kids[0].clone()
      },
      _ => (),
    }
    self.op(Operator::Not, vec![ term ])
  }

  /** Creates a conjunction. */
  pub fn and(& self, mut kids: Vec<Term>) -> Term {
    debug_assert!(kids.len() > 0) ;
    if kids.len() == 1 { kids.pop().unwrap() } else {
      self.op(Operator::And, kids)
    }
  }

  /** Creates a conjunction. */
  pub fn or(& self, mut kids: Vec<Term>) -> Term {
    debug_assert!(kids.len() > 0) ;
    if kids.len() == 1 { kids.pop().unwrap() } else {
      self.op(Operator::Or, kids)
    }
  }

  /** Creates a conjunction. */
  pub fn xor(& self, mut kids: Vec<Term>) -> Term {
    debug_assert!(kids.len() > 0) ;
    if kids.len() == 1 { kids.pop().unwrap() } else {
      self.op(Operator::Xor, kids)
    }
  }

  /** Creates an implication. */
  pub fn imp(& self, lhs: Term, rhs: Term) -> Term {
    self.op(Operator::Impl, vec![lhs, rhs])
  }

  /** Creates an addition. */
  pub fn add(& self, mut kids: Vec<Term>) -> Term {
    debug_assert!(kids.len() > 0) ;
    if kids.len() == 1 { kids.pop().unwrap() } else {
      self.op(Operator::Add, kids)
    }
  }

  /** Creates a substraction. */
  pub fn sub(& self, mut kids: Vec<Term>) -> Term {
    debug_assert!(kids.len() > 0) ;
    if kids.len() == 1 { kids.pop().unwrap() } else {
      self.op(Operator::Sub, kids)
    }
  }

  /** Creates a numeric negation. */
  pub fn neg(& self, term: Term) -> Term {
    match * term.get() {
      RealTerm::C( ref c ) => match * c.get() {
        RealCst::Int(ref i) => return self.cst(- i),
        RealCst::Rat(ref r) => return self.cst(- r),
        _ => (),
      },
      _ => (),
    } ;
    self.op(Operator::Neg, vec![ term ])
  }

  /** Creates a multiplication. */
  pub fn mul(& self, mut kids: Vec<Term>) -> Term {
    debug_assert!(kids.len() > 0) ;
    if kids.len() == 1 { kids.pop().unwrap() } else {
      self.op(Operator::Mul, kids)
    }
  }

  /** Creates a division. */
  pub fn div(& self, lhs: Term, rhs: Term) -> Term {
    self.op(Operator::Div, vec![ lhs, rhs ])
  }

  /** Creates a less than or equal. */
  pub fn le(& self, lhs: Term, rhs: Term) -> Term {
    self.op(Operator::Le, vec![ lhs, rhs])
  }

  /** Creates a greater than or equal. */
  pub fn ge(& self, lhs: Term, rhs: Term) -> Term {
    self.op(Operator::Gt, vec![ lhs, rhs])
  }

  /** Creates a less than. */
  pub fn lt(& self, lhs: Term, rhs: Term) -> Term {
    self.op(Operator::Lt, vec![ lhs, rhs])
  }

  /** Creates a greater than. */
  pub fn gt(& self, lhs: Term, rhs: Term) -> Term {
    self.op(Operator::Gt, vec![ lhs, rhs])
  }

  /** Evaluates a term. */
  pub fn eval(
    & self, term: & Term, off: & Offset2, model: & ::Model
  ) -> Result<Cst, String> {
    ::term::eval::eval(& self, term, off, model)
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

impl CstMaker<Cst, Term> for Factory {
  fn cst(& self, cst: Cst) -> Term {
    self.term.cst(cst)
  }
}
impl CstMaker<Bool, Term> for Factory {
  fn cst(& self, cst: Bool) -> Term {
    use cst::ConstMaker ;
    self.term.cst( self.cst.constant(cst) )
  }
}
impl CstMaker<Int, Term> for Factory {
  fn cst(& self, cst: Int) -> Term {
    use cst::ConstMaker ;
    self.term.cst( self.cst.constant(cst) )
  }
}
impl CstMaker<Rat, Term> for Factory {
  fn cst(& self, cst: Rat) -> Term {
    use cst::ConstMaker ;
    self.term.cst( self.cst.constant(cst) )
  }
}
impl CstMaker<Bool, Cst> for Factory {
  fn cst(& self, cst: Bool) -> Cst {
    use cst::ConstMaker ;
    self.cst.constant(cst)
  }
}
impl CstMaker<Int, Cst> for Factory {
  fn cst(& self, cst: Int) -> Cst {
    use cst::ConstMaker ;
    self.cst.constant(cst)
  }
}
impl CstMaker<Rat, Cst> for Factory {
  fn cst(& self, cst: Rat) -> Cst {
    use cst::ConstMaker ;
    self.cst.constant(cst)
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
impl VarMaker<Sym, Var> for Factory {
  fn var(& self, sym: Sym) -> Var { self.var.var(sym) }
  fn svar(& self, sym: Sym, st: State) -> Var { self.var.svar(sym,st) }
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
    if bindings.len() > 0 {
      self.term.let_b(bindings, term)
    } else { term }
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
  type I = Offset2 ;
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
    parser::cst_parser(bytes, self)
  }
  fn parse_expr<'a>(
    & self, bytes: & 'a [u8], off: & Offset2
  ) -> IResult<'a, & 'a [u8], (Term, Smt2Offset)> {
    parser::smt2::term_parser(bytes, self, off)
  }
  fn parse_proof<'a>(
    & self, _: & 'a [u8]
  ) -> IResult<'a, & 'a [u8], ()> {
    unimpl!()
  }
}


/** Parsers for TSV Systems */
pub trait ParseSts2 {
  /** Type of identifiers when parsing an TSV system. */
  type Ident ;
  /** Type for the result of expression parsing. */
  type ExprRes ;
  /** Type of types when parsing an TSV system. */
  type Type ;
  /** Parses an identifier in TSV format. */
  fn parse_ident<'a>(
    & self, bytes: & 'a [u8]
  ) -> IResult<'a, & 'a [u8], Self::Ident> ;
  /** Parses an expression in TSV format. */
  fn parse_expr<'a>(
    & self, bytes: & 'a [u8]
  ) -> IResult<'a, & 'a [u8], Self::ExprRes> ;
  /** Parses a Type in TSV format. */
  fn parse_type<'a>(
    & self, bytes: & 'a [u8]
  ) -> IResult<'a, & 'a [u8], Self::Type> ;
}

impl ParseSts2 for Factory {
  type Ident = Sym ;
  type ExprRes = TermAndDep ;
  type Type = Type ;
  fn parse_ident<'a>(
    & self, bytes: & 'a [u8]
  ) -> IResult<'a, & 'a [u8], Sym> {
    map!(
      bytes,
      parser::tsv::id_parser,
      |sym| self.sym(sym)
    )
  }
  fn parse_expr<'a>(
    & self, bytes: & 'a [u8]
  ) -> IResult<'a, & 'a [u8], TermAndDep> {
    parser::tsv::term_parser(bytes, self)
  }
  fn parse_type<'a>(
    & self, bytes: & 'a [u8]
  ) -> IResult<'a, & 'a [u8], Type> {
    parser::type_parser(bytes)
  }
}
