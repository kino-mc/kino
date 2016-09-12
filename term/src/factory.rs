// Copyright 2015 Adrien Champion. See the COPYRIGHT file at the top-level
// directory of this distribution.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

/*! Term factory stuff. */

use std::collections::HashMap ;
use std::sync::{ Mutex, Arc } ;

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
  bump, debump
} ;
use parser ;
use parser::vmt::TermAndDep ;

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

/// Factory for terms.
#[derive(Clone)]
pub struct Factory {
  /// Hash cons table for function symbols.
  sym: SymConsign,
  /// Hash cons table for variables.
  var: VarConsign,
  /// Hash cons table for constants.
  cst: CstConsign,
  /// Hash cons table for terms.
  term: TermConsign,
  /// Maps terms to types, scoped. Lazy, computes types on demand.
  ///
  /// To use, make sure you manually insert the type of variables.
  scoped_types: Arc< Mutex< HashMap<(Sym, Term), Type> > >,
  /// Maps terms to types, global. Lazy, computes types on demand.
  ///
  /// To use, make sure you manually insert the type of variables.
  unscoped_types: Arc< Mutex< HashMap<Term, Type> > >,
  /// Maps function symbols to their type.
  fun_types: Arc< Mutex< HashMap<Sym, Type> > >,
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
  /// Creates an empty term factory.
  #[inline]
  pub fn mk() -> Self {
    Factory {
      sym: SymConsign::mk(),
      var: VarConsign::mk(),
      cst: CstConsign::mk(),
      term: TermConsign::mk(),
      scoped_types: Arc::new(
        Mutex::new( HashMap::with_capacity(107) )
      ),
      unscoped_types: Arc::new(
        Mutex::new( HashMap::with_capacity(107) )
      ),
      fun_types: Arc::new(
        Mutex::new( HashMap::with_capacity(107) )
      ),
    }
  }

  /// An iterator over the constants in the factory.
  #[inline]
  pub fn cst_fold<
    T, F: Fn(T, & Cst) -> T
  >(& self, init: T, f: F) -> T {
    self.cst.lock().unwrap().iter().fold(
      init, | data, (_, snd) | f(data, snd)
    )
  }

  /// Inserts a type for a variable without doing anything else.
  pub fn set_fun_type(
    & self, sym: Sym, typ: Type
  ) -> Result<(), String> {
    let sym_bak = sym.clone() ;
    match self.fun_types.lock().unwrap().insert( sym, typ ) {
      Some(t) if t != typ => Err(
        format!(
          "trying to redefine type of function {} from {} to {}",
          sym_bak, t, typ
        )
      ),
      _ => Ok(())
    }
  }

  /// Inserts a type for a variable without doing anything else.
  fn set_type_unsafe(
    & self, sym: Option<Sym>, term: Term, typ: Type
  ) -> Result<(), String> {
    let t_bak = term.clone() ;
    match sym {
      Some(sym) => {
        let sym_bak = sym.clone() ;
        match self.scoped_types.lock().unwrap().insert( (sym, term), typ ) {
          Some(t) if t != typ => Err(
            format!(
              "trying to redefine type of {}::{} from {} to {}",
              sym_bak, t_bak, t, typ
            )
          ),
          _ => Ok(())
        }
      },
      None => match self.unscoped_types.lock().unwrap().insert( term, typ ) {
        Some(t) if t != typ => Err(
          format!(
            "trying to redefine type of {} from {} to {}",
            t_bak, t, typ
          )
        ),
        _ => Ok(())
      },
    }
  }

  /// Inserts a type for a variable, under a scope.
  ///
  /// For state variables, automatically also adds the next (current) version
  /// when inserting the current (next) version.
  ///
  /// Setting a different type for an already typed variable is an error.
  pub fn set_var_type(
    & self, sym: Option<Sym>, v: Var, typ: Type
  ) -> Result<(), String> {
    match v.state() {
      None => {
        let var = self.mk_var(v) ;
        self.set_type_unsafe(sym, var, typ)
      },
      Some(state) => {
        let var: Term = self.mk_var(v) ;
        try!( self.set_type_unsafe(sym.clone(), var.clone(), typ) ) ;
        let var: Term = try!(
          match state {
            // Neither of these two can be an error.
            State::Curr => self.bump(var),
            State::Next => self.debump(var),
          }
        ) ;
        self.set_type_unsafe(sym, var, typ)
      },
    }
  }

  /// Returns the type of a term under some scope. Cached.
  ///
  /// **Mostly unimplemented currently. Can only type the variables added with
  /// `set_var_type`.**
  ///
  /// To use, make sure you manually insert the type of variables and the
  /// function symbols.
  ///
  /// Can result in an error if some type information about some leaves of
  /// the term is unknown.
  pub fn type_of(
    & self, term: & Term, scope: Option<Sym>
  ) -> Result<Type, String> {
    match scope {
      Some(scope) => {
        match self.scoped_types.lock().unwrap().get(
          & (scope.clone(), term.clone())
        ) {
          Some(typ) => Ok(* typ),
          None => Err(
            format!("can't type unknown term {} under scope {}", term, scope)
          ),
        }
      },
      None => {
        match self.unscoped_types.lock().unwrap().get( term ) {
          Some(typ) => Ok(* typ),
          None => Err(
            format!("can't type unknown term {}", term)
          ),
        }
      },
    }
  }

  /// Parses a type.
  pub fn parse_type<'a>(bytes: & 'a [u8]) -> IResult<& 'a [u8], Type> {
    parser::type_parser(bytes)
  }

  /// Creates a variable from a `Var`.
  pub fn mk_var(& self, var: Var) -> Term {
    self.term.var(var)
  }

  /// Creates a constant from a `Cst`.
  pub fn mk_cst(& self, cst: Cst) -> Term {
    self.term.cst(cst)
  }

  /// Creates a constant from a real `Cst`.
  pub fn mk_rcst(& self, cst: ::real_term::Cst) -> Cst {
    use cst::ConstMaker ;
    self.cst.constant(cst)
  }



  /// Creates an n-ary equality.
  pub fn eq(& self, kids: Vec<Term>) -> Term {
    debug_assert!(kids.len() > 1) ;
    self.op(Operator::Eq, kids)
  }

  /// Creates an if-then-else.
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

  /// Creates a negation.
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
      RealTerm::Op(Operator::Le, ref kids) => {
        debug_assert!(kids.len() == 2) ;
        return self.op(
          Operator::Gt, kids.clone()
        )
      },
      RealTerm::Op(Operator::Lt, ref kids) => {
        debug_assert!(kids.len() == 2) ;
        return self.op(
          Operator::Ge, kids.clone()
        )
      },
      RealTerm::Op(Operator::Ge, ref kids) => {
        debug_assert!(kids.len() == 2) ;
        return self.op(
          Operator::Lt, kids.clone()
        )
      },
      RealTerm::Op(Operator::Gt, ref kids) => {
        debug_assert!(kids.len() == 2) ;
        return self.op(
          Operator::Le, kids.clone()
        )
      },
      _ => (),
    }
    self.op(Operator::Not, vec![ term ])
  }

  /// Creates a conjunction.
  pub fn and(& self, mut kids: Vec<Term>) -> Term {
    debug_assert!(kids.len() > 0) ;
    if kids.len() == 1 { kids.pop().unwrap() } else {
      self.op(Operator::And, kids)
    }
  }

  /// Creates a conjunction.
  pub fn or(& self, mut kids: Vec<Term>) -> Term {
    debug_assert!(kids.len() > 0) ;
    if kids.len() == 1 { kids.pop().unwrap() } else {
      self.op(Operator::Or, kids)
    }
  }

  /// Creates a conjunction.
  pub fn xor(& self, mut kids: Vec<Term>) -> Term {
    debug_assert!(kids.len() > 0) ;
    if kids.len() == 1 { kids.pop().unwrap() } else {
      self.op(Operator::Xor, kids)
    }
  }

  /// Creates an implication.
  pub fn imp(& self, lhs: Term, rhs: Term) -> Term {
    self.op(Operator::Impl, vec![lhs, rhs])
  }

  /// Creates an addition.
  pub fn add(& self, mut kids: Vec<Term>) -> Term {
    debug_assert!(kids.len() > 0) ;
    if kids.len() == 1 { kids.pop().unwrap() } else {
      self.op(Operator::Add, kids)
    }
  }

  /// Creates a substraction.
  pub fn sub(& self, mut kids: Vec<Term>) -> Term {
    debug_assert!(kids.len() > 0) ;
    if kids.len() == 1 { kids.pop().unwrap() } else {
      self.op(Operator::Sub, kids)
    }
  }

  /// Creates a numeric negation.
  pub fn neg(& self, term: Term) -> Term {
    match * term.get() {
      RealTerm::C( ref c ) => match * c.get() {
        RealCst::Int(ref i) => return self.cst(- i),
        RealCst::Rat(ref r) => return self.cst(- r),
        _ => (),
      },
      _ => (),
    } ;
    self.op(Operator::Sub, vec![ term ])
  }

  /// Creates a multiplication.
  pub fn mul(& self, mut kids: Vec<Term>) -> Term {
    debug_assert!(kids.len() > 0) ;
    if kids.len() == 1 { kids.pop().unwrap() } else {
      self.op(Operator::Mul, kids)
    }
  }

  /// Creates a division.
  pub fn div(& self, lhs: Term, rhs: Term) -> Term {
    self.op(Operator::Div, vec![ lhs, rhs ])
  }

  /// Creates a less than or equal.
  pub fn le(& self, lhs: Term, rhs: Term) -> Term {
    self.op(Operator::Le, vec![ lhs, rhs])
  }

  /// Creates a greater than or equal.
  pub fn ge(& self, lhs: Term, rhs: Term) -> Term {
    self.op(Operator::Gt, vec![ lhs, rhs])
  }

  /// Creates a less than.
  pub fn lt(& self, lhs: Term, rhs: Term) -> Term {
    self.op(Operator::Lt, vec![ lhs, rhs])
  }

  /// Creates a greater than.
  pub fn gt(& self, lhs: Term, rhs: Term) -> Term {
    self.op(Operator::Gt, vec![ lhs, rhs])
  }

  /// Evaluates a term.
  pub fn eval(
    & self, term: & Term, off: & Offset2, model: & ::Model, scope: Sym
  ) -> Result<Cst, String> {
    ::term::eval::eval(& self, term, off, model, scope)
  }

  /// Evaluates a term to a bool value.
  pub fn eval_bool(
    & self, term: & Term, off: & Offset2, model: & ::Model, scope: Sym
  ) -> Result<Bool, String> {
    use ::real_term::Cst::* ;
    match ::term::eval::eval(& self, term, off, model, scope) {
      Ok(val) => match * val.get() {
        Bool(ref b) => Ok(* b),
        Int(ref i) => Err(
          format!("[eval_bool] got integer value {}", i)
        ),
        Rat(ref r) => Err(
          format!("[eval_bool] got rational value {}", r)
        ),
      },
      Err(e) => Err(e),
    }
  }

  /// Evaluates a term to an integer value.
  pub fn eval_int(
    & self, term: & Term, off: & Offset2, model: & ::Model, scope: Sym
  ) -> Result<Int, String> {
    use ::real_term::Cst::* ;
    match ::term::eval::eval(& self, term, off, model, scope) {
      Ok(val) => match * val.get() {
        Int(ref i) => Ok(i.clone()),
        Bool(ref b) => Err(
          format!("[eval_int] got bool value {}", b)
        ),
        Rat(ref r) => Err(
          format!("[eval_int] got rational value {}", r)
        ),
      },
      Err(e) => Err(e),
    }
  }

  /// Evaluates a term to an integer value.
  pub fn eval_rat(
    & self, term: & Term, off: & Offset2, model: & ::Model, scope: Sym
  ) -> Result<Rat, String> {
    use ::real_term::Cst::* ;
    match ::term::eval::eval(& self, term, off, model, scope) {
      Ok(val) => match * val.get() {
        Rat(ref r) => Ok(r.clone()),
        Bool(ref b) => Err(
          format!("[eval_int] got bool value {}", b)
        ),
        Int(ref i) => Err(
          format!("[eval_int] got integer value {}", i)
        ),
      },
      Err(e) => Err(e),
    }
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

/// Unary operations on terms.
pub trait UnTermOps<Trm> {
  /** Bumps a term.

  * changes all `SVar(sym, State::curr)` to `SVar(sym, State::next)`,
  * returns `Err(())` if input term contains a `SVar(_, State::next)`. */
  fn bump(& self, Trm) -> Result<Term,String> ;
  /** Bumps a term.

  * changes all `SVar(sym, State::next)` to `SVar(sym, State::curr)`,
  * returns `Err(())` if input term contains a `SVar(_, State::curr)`. */
  fn debump(& self, Trm) -> Result<Term,String> ;
}
// impl<
//   'a, Trm: Clone, T: UnTermOps<Trm> + Sized
// > UnTermOps<& 'a Trm> for T {
//   #[inline(always)]
//   fn bump(& self, term: & 'a Trm) -> Result<Term,String> {
//     (self as & UnTermOps<Trm>).bump(term.clone())
//   }
//   #[inline(always)]
//   fn debump(& self, term: & 'a Trm) -> Result<Term,String> {
//     (self as & UnTermOps<Trm>).debump(term.clone())
//   }
// }

impl UnTermOps<Term> for Factory {
  fn bump(& self, term: Term) -> Result<Term,String> {
    bump(self, term)
  }
  fn debump(& self, term: Term) -> Result<Term,String> {
    debump(self, term)
  }
}

impl<'a> UnTermOps<& 'a Term> for Factory {
  fn bump(& self, term: & 'a Term) -> Result<Term,String> {
    self.bump( term.clone() )
  }
  fn debump(& self, term: & 'a Term) -> Result<Term,String> {
    self.debump( term.clone() )
  }
}







impl ParseSmt2 for Factory {
  type Ident = (Var, Option<Offset>) ;
  type Value = Cst ;
  type Expr = (Term, Smt2Offset) ;
  type Proof = () ;
  type I = Offset2 ;
  fn parse_ident<'a>(
    & self, bytes: & 'a [u8]
  ) -> IResult<& 'a [u8], (Var, Option<Offset>)> {
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
  ) -> IResult<& 'a [u8], Cst> {
    parser::cst_parser(bytes, self)
  }
  fn parse_expr<'a>(
    & self, bytes: & 'a [u8], off: & Offset2
  ) -> IResult<& 'a [u8], (Term, Smt2Offset)> {
    parser::smt2::term_parser(bytes, self, off)
  }
  fn parse_proof<'a>(
    & self, _: & 'a [u8]
  ) -> IResult<& 'a [u8], ()> {
    unimpl!()
  }
}


/** Parsers for VMT Systems */
pub trait ParseVmt2 {
  /** Type of identifiers when parsing an VMT system. */
  type Ident ;
  /** Type for the result of expression parsing. */
  type ExprRes ;
  /** Type of types when parsing an VMT system. */
  type Type ;
  /** Parses an identifier in VMT format. */
  fn parse_ident<'a>(
    & self, bytes: & 'a [u8]
  ) -> IResult<& 'a [u8], Self::Ident> ;
  /** Parses an expression in VMT format. */
  fn parse_expr<'a>(
    & self, bytes: & 'a [u8]
  ) -> IResult<& 'a [u8], Self::ExprRes> ;
  /** Parses a Type in VMT format. */
  fn parse_type<'a>(
    & self, bytes: & 'a [u8]
  ) -> IResult<& 'a [u8], Self::Type> ;
}

impl ParseVmt2 for Factory {
  type Ident = Sym ;
  type ExprRes = TermAndDep ;
  type Type = Type ;
  fn parse_ident<'a>(
    & self, bytes: & 'a [u8]
  ) -> IResult<& 'a [u8], Sym> {
    map!(
      bytes,
      parser::vmt::id_parser,
      |sym| self.sym(sym)
    )
  }
  fn parse_expr<'a>(
    & self, bytes: & 'a [u8]
  ) -> IResult<& 'a [u8], TermAndDep> {
    parser::vmt::term_parser(bytes, self)
  }
  fn parse_type<'a>(
    & self, bytes: & 'a [u8]
  ) -> IResult<& 'a [u8], Type> {
    parser::type_parser(bytes)
  }
}
