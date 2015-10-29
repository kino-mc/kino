// Copyright 2015 Adrien Champion. See the COPYRIGHT file at the top-level
// directory of this distribution.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

/** Term structures and parsers. */

use ::base::* ;
use ::typ ;
use ::sym ;
use ::cst ;
use self::TerM::* ;

#[derive(Debug,Clone,Copy,PartialEq,Eq,PartialOrd,Ord,Hash)]
pub enum State {
  Curr, Next
}

#[derive(Debug,PartialEq,Eq,PartialOrd,Ord,Hash)]
pub enum TerM {
  Var(sym::Sym),
  SVar(sym::Sym, State),
  Cst(cst::Cst),
  App(sym::Sym, Vec<Term>),
  Forall(Vec<(sym::Sym, typ::Type)>, Term),
  Exists(Vec<(sym::Sym, typ::Type)>, Term),
  Let(Vec<(sym::Sym, Term)>, Term),
}

pub type Term = HConsed<TerM> ;
pub type TermConsign = HConsign<TerM> ;

pub trait VarMaker<Sym> {
  fn var(& self, Sym) -> Term ;
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
impl VarMaker<sym::Sym> for TermConsign {
  fn var(& self, id: sym::Sym) -> Term {
    self.lock().unwrap().mk( Var(id) )
  }
  fn svar(& self, id: sym::Sym, state: State) -> Term {
    self.lock().unwrap().mk( SVar(id, state) )
  }
}

trait CstMaker<Const> {
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

pub trait AppMaker<Id> {
  fn app(& self, Id, Vec<Term>) -> Term ;
}
impl<
  'a, Id: Clone, T: Sized + AppMaker<Id>
> AppMaker<& 'a Id> for T {
  fn app(& self, id: & 'a Id, args: Vec<Term>) -> Term {
    (self as & AppMaker<Id>).app(id.clone(), args)
  }
}
impl AppMaker<sym::Sym> for TermConsign {
  fn app(& self, id: sym::Sym, args: Vec<Term>) -> Term {
    self.lock().unwrap().mk( App(id, args) )
  }
}

pub trait BindMaker<Trm> {
  fn forall(& self, Vec<(sym::Sym, typ::Type)>, Trm) -> Term ;
  fn exists(& self, Vec<(sym::Sym, typ::Type)>, Trm) -> Term ;
  fn let_b(& self, Vec<(sym::Sym, Term)>, Trm) -> Term ;
}
impl<
  'a, Trm: Clone, T: Sized + BindMaker<Trm>
> BindMaker<& 'a Trm> for T {
  fn forall(& self, bind: Vec<(sym::Sym, typ::Type)>, term: & 'a Trm) -> Term {
    self.forall( bind, term.clone() )
  }
  fn exists(& self, bind: Vec<(sym::Sym, typ::Type)>, term: & 'a Trm) -> Term {
    self.exists( bind, term.clone() )
  }
  fn let_b(& self, bind: Vec<(sym::Sym, Term)>, term: & 'a Trm) -> Term {
    self.let_b( bind, term.clone() )
  }
}
impl BindMaker<Term> for TermConsign {
  fn forall(& self, bind: Vec<(sym::Sym, typ::Type)>, term: Term) -> Term {
    self.lock().unwrap().mk( Forall(bind, term) )
  }
  fn exists(& self, bind: Vec<(sym::Sym, typ::Type)>, term: Term) -> Term {
    self.lock().unwrap().mk( Exists(bind, term) )
  }
  fn let_b(& self, bind: Vec<(sym::Sym, Term)>, term: Term) -> Term {
    self.lock().unwrap().mk( Let(bind, term) )
  }
}

pub trait UnTermOps<Trm> {
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





mod zip {
  use super::* ;
  use ::sym ;
  use ::typ ;

  use self::Res::* ;
  use self::Step::* ;

  enum Res {
    Done(Term), NYet(Zip)
  }

  enum Step {
    App(
      sym::Sym, Vec<Term>, Vec<Term>
    ),
    Forall(
      Vec<(sym::Sym, typ::Type)>
    ),
    Exists(
      Vec<(sym::Sym, typ::Type)>
    ),
    Let1(
      Vec<(sym::Sym, Term)>
    ),
    Let2(
      Vec<(sym::Sym, Term)>, sym::Sym, Vec<(sym::Sym, Term)>, Term
    ),
  }

  struct Zip {
    path: Vec<Step>,
    curr: Term,
  }

  impl Zip {

    pub fn go_down(mut self) -> Self {
      loop {
        let update = match * self.curr.get() {

          TerM::App(ref sym, ref terms) => {
            let mut terms = terms.clone() ;
            if let Some(term) = terms.pop() {
              self.path.push( App(sym.clone(), vec![], terms) ) ;
              Some( term.clone() )
            } else {
              panic!("application to nothing: {:?}", sym)
            }
          },

          TerM::Forall(ref syms, ref term) => {
            self.path.push( Forall(syms.clone()) ) ;
            Some( term.clone() )
          },

          TerM::Exists(ref syms, ref term) => {
            self.path.push( Exists(syms.clone()) ) ;
            Some( term.clone() )
          },

          TerM::Let(ref syms, ref term) => {
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