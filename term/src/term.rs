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

#[derive(PartialEq,Eq,PartialOrd,Ord,Hash)]
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