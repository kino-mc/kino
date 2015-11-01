// Copyright 2015 Adrien Champion. See the COPYRIGHT file at the top-level
// directory of this distribution.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

/*! Terms. */

use std::io ;

use ::base::{ PrintSmt2, Offset2, HConsed, HConsign, State } ;
use ::typ::Type ;
use ::sym::Sym ;
use ::cst ;
use self::RealTerm::* ;

/** Standard operators. */
#[derive(Debug,Clone,Copy,PartialEq,Eq,PartialOrd,Ord,Hash)]
pub enum Operator {
  /** If then else operator. */
  Ite,
  /** Negation operator. */
  Not,
  /** Conjunction operator. */
  And,
  /** Disjunction operator. */
  Or,
  /** Implication operator. */
  Impl,
  /** Exclusive disjunction operator. */
  Xor,
  /** Distinct operator. */
  Distinct,
  /** Plus operator. */
  Add,
  /** Minus operator. */
  Sub,
  /** Unary minus operator. */
  Neg,
  /** Multiplication operator. */
  Mul,
  /** Division operator. */
  Div,
  /** Less or equal operator. */
  Le,
  /** Greater or equal operator. */
  Ge,
  /** Less than operator. */
  Lt,
  /** Greater than operator. */
  Gt,
}

impl PrintSmt2 for Operator {
  fn to_smt2(
    & self, writer: & mut io::Write, _: & Offset2
  ) -> io::Result<()> {
    write!(
      writer,
      "{}",
      match * self {
        Operator::Ite => "ite",
        Operator::Not => "not",
        Operator::And => "and",
        Operator::Or => "or",
        Operator::Impl => "impl",
        Operator::Xor => "xor",
        Operator::Distinct => "distinct",
        Operator::Add => "+",
        Operator::Sub => "-",
        Operator::Neg => "-",
        Operator::Mul => "*",
        Operator::Div => "/",
        Operator::Le => "<=",
        Operator::Ge => ">=",
        Operator::Lt => "<",
        Operator::Gt => ">",
      }
    )
  }
}

/** Underlying representation of terms. */
#[derive(Debug,PartialEq,Eq,PartialOrd,Ord,Hash)]
pub enum RealTerm {
  /** A non-stateful variable. */
  Var(Sym),
  /** A stateful variable. */
  SVar(Sym, State),
  /** A constant value. */
  Cst(cst::Cst),
  /** An application of an operator. */
  Op(Operator, Vec<Term>),
  /** A universal quantification. */
  Forall(Vec<(Sym, Type)>, Term),
  /** An existential quantification. */
  Exists(Vec<(Sym, Type)>, Term),
  /** A let-binding. */
  Let(Vec<(Sym, Term)>, Term),
  /** An application of a function symbol. */
  App(Sym, Vec<Term>),
}

/** Hash consed term. */
pub type Term = HConsed<RealTerm> ;

/** Hash cons table for terms. */
pub type TermConsign = HConsign<RealTerm> ;

impl PrintSmt2 for Term {
  fn to_smt2(
    & self, writer: & mut io::Write, offset: & Offset2
  ) -> io::Result<()> {
    let mut stack = vec![ (true, vec![ self.clone() ]) ] ;
    loop {
      if let Some( (is_first, mut to_do) ) = stack.pop() {

        if let Some( term ) = to_do.pop() {
          stack.push( (false, to_do) ) ;
          if ! is_first { try!( write!(writer, " ") ) } ;
          match term.get() {
            & Var(ref sym) => {
              try!( write!(writer, "|") ) ;
              try!( sym.to_smt2(writer, offset) ) ;
              try!( write!(writer, "|") )
            },
            & SVar(ref sym, ref state) => {
              try!( write!(writer, "|@") ) ;
              try!( offset[state].to_smt2(writer, offset) ) ;
              try!( sym.to_smt2(writer, offset) ) ;
              try!( write!(writer, "|") )
            },
            & Cst(ref cst) => {
              try!( cst.to_smt2(writer, offset) )
            },
            & App(ref sym, ref args) => {
              try!( write!(writer, "(|") ) ;
              try!( sym.to_smt2(writer, offset) ) ;
              try!( write!(writer, "| ") ) ;
              let mut args = args.clone() ;
              args.reverse() ;
              stack.push( (true, args) )
            },
            & Op(ref op, ref args) => {
              try!( write!(writer, "(") ) ;
              try!( op.to_smt2(writer, offset) ) ;
              try!( write!(writer, " ") ) ;
              let mut args = args.clone() ;
              args.reverse() ;
              stack.push( (true, args) )
            },
            _ => unimpl!(),
          } ;
        } else {
          // Don't close paren for the last element of the stack.
          if ! stack.is_empty() {
            try!( write!(writer, ")") )
          }
        }

      } else {
        break
      }
    } ;
    Ok(())
  }
}

/** Can create non-stateful stateful variables. */
pub trait VarMaker<Sym> {
  /** Creates a non-stateful variable. */
  #[inline]
  fn var(& self, Sym) -> Term ;
  /** Creates a stateful variable. */
  #[inline]
  fn svar(& self, Sym, State) -> Term ;
}
impl<
  'a, Sym: Clone, T: Sized + VarMaker<Sym>
> VarMaker<& 'a Sym> for T {
  fn var(& self, id: & 'a Sym) -> Term {
    (self as & VarMaker<Sym>).var(id.clone())
  }
  fn svar(& self, id: & 'a Sym, state: State) -> Term {
    (self as & VarMaker<Sym>).svar(id.clone(), state)
  }
}
impl VarMaker<Sym> for TermConsign {
  fn var(& self, id: Sym) -> Term {
    self.lock().unwrap().mk( Var(id) )
  }
  fn svar(& self, id: Sym, state: State) -> Term {
    self.lock().unwrap().mk( SVar(id, state) )
  }
}

/** Can create a constant value. */
pub trait CstMaker<Const> {
  /** Creates a constant value. */
  #[inline]
  fn cst(& self, Const) -> Term ;
}
impl<
  'a, Const: Clone, T: Sized + CstMaker<Const>
> CstMaker<& 'a Const> for T {
  fn cst(& self, c: & 'a Const) -> Term {
    self.cst(c.clone())
  }
}
impl CstMaker<cst::Cst> for TermConsign {
  fn cst(& self, c: cst::Cst) -> Term {
    self.lock().unwrap().mk( Cst(c) )
  }
}

/** Can create an application of an operator. */
pub trait OpMaker {
  /** Creates an application of an operator. */
  #[inline]
  fn op(& self, Operator, Vec<Term>) -> Term ;
}
impl OpMaker for TermConsign {
  fn op(& self, op: Operator, args: Vec<Term>) -> Term {
    self.lock().unwrap().mk( Op(op, args) )
  }
}

/** Can create an application of a function symbol. */
pub trait AppMaker<Id> {
  /** Creates an application of a function symbol. */
  #[inline]
  fn app(& self, Id, Vec<Term>) -> Term ;
}
impl<
  'a, Id: Clone, T: Sized + AppMaker<Id>
> AppMaker<& 'a Id> for T {
  fn app(& self, id: & 'a Id, args: Vec<Term>) -> Term {
    (self as & AppMaker<Id>).app(id.clone(), args)
  }
}
impl AppMaker<Sym> for TermConsign {
  fn app(& self, id: Sym, args: Vec<Term>) -> Term {
    self.lock().unwrap().mk( App(id, args) )
  }
}

/** Can create quantified terms and let-bindings. */
pub trait BindMaker<Trm> {
  /** Creates a universal quantification over some symbols. */
  #[inline]
  fn forall(& self, Vec<(Sym, Type)>, Trm) -> Term ;
  /** Creates an existential quantification over some symbols. */
  #[inline]
  fn exists(& self, Vec<(Sym, Type)>, Trm) -> Term ;
  /** Creates a let-binding. */
  #[inline]
  fn let_b(& self, Vec<(Sym, Term)>, Trm) -> Term ;
}
impl<
  'a, Trm: Clone, T: Sized + BindMaker<Trm>
> BindMaker<& 'a Trm> for T {
  fn forall(& self, bind: Vec<(Sym, Type)>, term: & 'a Trm) -> Term {
    self.forall( bind, term.clone() )
  }
  fn exists(& self, bind: Vec<(Sym, Type)>, term: & 'a Trm) -> Term {
    self.exists( bind, term.clone() )
  }
  fn let_b(& self, bind: Vec<(Sym, Term)>, term: & 'a Trm) -> Term {
    self.let_b( bind, term.clone() )
  }
}
impl BindMaker<Term> for TermConsign {
  fn forall(& self, bind: Vec<(Sym, Type)>, term: Term) -> Term {
    self.lock().unwrap().mk( Forall(bind, term) )
  }
  fn exists(& self, bind: Vec<(Sym, Type)>, term: Term) -> Term {
    self.lock().unwrap().mk( Exists(bind, term) )
  }
  fn let_b(& self, bind: Vec<(Sym, Term)>, term: Term) -> Term {
    self.lock().unwrap().mk( Let(bind, term) )
  }
}

/** Unary operations over terms. */
pub trait UnTermOps<Trm> {
  /** Bumps a term.

  * changes all `SVar(sym, State::curr)` to `SVar(sym, State::next)`,
  * returns `Err(())` if input term contains a `SVar(_, State::next)`. */
  #[inline]
  fn bump(& self, Trm) -> Result<Term,()> ;
}
impl<
  'a, Trm: Clone, T: Sized + UnTermOps<Trm>
> UnTermOps<& 'a Trm> for T {
  fn bump(& self, term: & 'a Trm) -> Result<Term,()> {
    self.bump( term.clone() )
  }
}
impl UnTermOps<Term> for TermConsign {
  fn bump(& self, term: Term) -> Result<Term,()> {
    zip::var_map(
      self,
      |cons, t| match * t.get() {
        SVar(ref s, State::Curr) => Ok(
          Some( cons.svar(s, State::Next) )
        ),
        SVar(_,_) => Err(()),
        _ => Ok(None),
      },
      term
    )
  }
}




/** Zipper stuff. */
mod zip {
  use super::* ;
  use ::sym::Sym ;
  use ::typ::Type ;

  use self::Res::* ;
  use self::Step::* ;

  /** Result of going up in a zipper. */
  enum Res {
    /** Zipper is done, contains the resulting term. */
    Done(Term),
    /** Zipper is not done, contains the new state of the zipper. */
    NYet(Zip)
  }

  /** A zipper step. */
  enum Step {
    /** We're below a function symbol application. */
    App(
      Sym, Vec<Term>, Vec<Term>
    ),
    /** We're below a universal quantifier. */
    Forall(
      Vec<(Sym, Type)>
    ),
    /** We're below an existential quantifier. */
    Exists(
      Vec<(Sym, Type)>
    ),
    /** We're below a let-binding, in the terms symbols are binded to. */
    Let1(
      Vec<(Sym, Term)>
    ),
    /** We're below a let-binding, in the term the let ranges over. */
    Let2(
      Vec<(Sym, Term)>, Sym, Vec<(Sym, Term)>, Term
    ),
  }

  /** A zipper on terms. */
  struct Zip {
    /** Path of steps leading to the current term. */
    path: Vec<Step>,
    /** Current term. */
    curr: Term,
  }

  impl Zip {
    /** Goes down the current term stops when it reaches a leaf.

    That is, a variable or a constant. */
    pub fn go_down(mut self) -> Self {
      loop {
        let update = match * self.curr.get() {

          RealTerm::App(ref sym, ref terms) => {
            let mut terms = terms.clone() ;
            if let Some(term) = terms.pop() {
              self.path.push( App(sym.clone(), vec![], terms) ) ;
              Some( term.clone() )
            } else {
              panic!("application to nothing: {:?}", sym)
            }
          },

          RealTerm::Forall(ref syms, ref term) => {
            self.path.push( Forall(syms.clone()) ) ;
            Some( term.clone() )
          },

          RealTerm::Exists(ref syms, ref term) => {
            self.path.push( Exists(syms.clone()) ) ;
            Some( term.clone() )
          },

          RealTerm::Let(ref syms, ref term) => {
            self.path.push( Let1(syms.clone()) ) ;
            Some( term.clone() )
          },

          _ => None,
        } ;

        match update {
          None => return self,
          Some(t) => self.curr = t,
        }
      }
    }

    /** Goes up in the zipper recursively.

    Stops if going up an empty path, or unexplored siblings are found. */
    pub fn go_up(mut self, cons: & TermConsign) -> Res {
      loop {
        match self.path.pop() {

          Some( App(sym, mut lft, mut rgt) ) => {
            lft.push(self.curr) ;
            if let Some(term) = rgt.pop() {
              // Not done if `rgt` is not empty.
              self.curr = term ;
              self.path.push( App(sym, lft, rgt) ) ;
              return NYet(self)
            } else {
              // Otherwise go up.
              self.curr = cons.app(sym, lft)
            }
          },

          Some( Forall(syms) ) =>
            self.curr = cons.forall(syms, self.curr),

          Some( Exists(syms) ) =>
            self.curr = cons.exists(syms, self.curr),

          Some( Let1(mut syms) ) => {
            if let Some( (sym, term) ) = syms.pop() {
              self.path.push( Let2(vec![], sym, syms, self.curr) ) ;
              self.curr = term ;
              return NYet(self)
            } else {
              // We're in a let of nothing, skipping it.
              ()
            }
          },

          Some( Let2(mut lft, sym, mut rgt, t) ) => {
            lft.push( (sym, self.curr) ) ;
            if let Some( (sym, term) ) = rgt.pop() {
              // Not done if `rgt` is not empty.
              self.curr = term ;
              self.path.push( Let2(lft, sym, rgt, t) ) ;
              return NYet(self)
            } else {
              // Otherwise go up.
              self.curr = cons.let_b(lft, t)
            }
          },

          None => return Done(self.curr),
        }
      }
    }
  }

  // pub fn fold<Out, F>(cons: TermConsign, f: F, term: Term, init: Out) -> Out
  // where F: Fn(Out, & Term) -> Out {
  //   let mut zip = Zip { path: vec![], curr: term, cons: cons } ;
  //   let mut out = init ;
  //   loop {
  //     zip = zip.go_down() ;
  //     out = f(out, & zip.curr) ;
  //     zip = match zip.go_up() {
  //       Done(term) => return out,
  //       NYet(zip) => zip,
  //     }
  //   }
  // }

  /** Applies some function to the variables in a term. */
  pub fn var_map<'a,F,E>(
    cons: & 'a TermConsign, f: F, term: Term
  ) -> Result<Term,E>
  where F: Fn(& 'a TermConsign, & Term) -> Result<Option<Term>,E> {
    let mut zip = Zip { path: vec![], curr: term } ;
    loop {
      zip = zip.go_down() ;
      zip.curr = match f(cons, & zip.curr) {
        Ok( Some(term) ) => term,
        Ok( None ) => zip.curr,
        Err(e) => return Err(e),
      } ;
      zip = match zip.go_up(cons) {
        Done(term) => return Ok(term),
        NYet(zip) => zip,
      }
    }
  }
}