/** Term structures and parsers. */

use ::base::* ;
use ::typ ;
use ::id ;
use self::TerM::* ;

#[derive(Debug,Clone,Copy,PartialEq,Eq,PartialOrd,Ord,Hash)]
pub enum State {
  One, Zero
}

#[derive(PartialEq,Eq,PartialOrd,Ord,Hash)]
pub enum TerM {
  Var(id::Id),
  SVar(id::Id, State),
  Bool(typ::Bool),
  Int(typ::Int),
  Rat(typ::Rat),
  App(id::Id, Vec<Term>),
  Forall(Vec<id::Id>, Term),
  Exists(Vec<id::Id>, Term),
  Let(Vec<(id::Id, Term)>, Term),
}

pub type Term = HConsed<TerM> ;
pub type TermConsign = HConsign<TerM> ;

pub trait VarMaker<Id> {
  fn var(& self, Id) -> Term ;
  fn svar(& self, Id, State) -> Term ;
}
impl<
  'a, Id: Clone, T: Sized + VarMaker<Id>
> VarMaker<& 'a Id> for T {
  fn var(& self, id: & 'a Id) -> Term {
    (self as & VarMaker<Id>).var(id.clone())
  }
  fn svar(& self, id: & 'a Id, state: State) -> Term {
    (self as & VarMaker<Id>).svar(id.clone(), state)
  }
}
impl VarMaker<id::Id> for TermConsign {
  fn var(& self, id: id::Id) -> Term {
    self.lock().unwrap().mk( Var(id) )
  }
  fn svar(& self, id: id::Id, state: State) -> Term {
    self.lock().unwrap().mk( SVar(id, state) )
  }
}

pub trait CstMaker<Cst> {
  fn cst(& self, Cst) -> Term ;
}
impl<
  'a, Cst: Clone, T: Sized + CstMaker<Cst>
> CstMaker<& 'a Cst> for T {
  fn cst(& self, cst: & 'a Cst) -> Term {
    (self as & CstMaker<Cst>).cst(cst.clone())
  }
}
impl CstMaker<typ::Bool> for TermConsign {
  fn cst(& self, b: typ::Bool) -> Term {
    self.lock().unwrap().mk( Bool(b) )
  }
}
impl CstMaker<typ::Int> for TermConsign {
  fn cst(& self, i: typ::Int) -> Term {
    self.lock().unwrap().mk( Int(i) )
  }
}
impl CstMaker<typ::Rat> for TermConsign {
  fn cst(& self, r: typ::Rat) -> Term {
    self.lock().unwrap().mk( Rat(r) )
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
impl AppMaker<id::Id> for TermConsign {
  fn app(& self, id: id::Id, args: Vec<Term>) -> Term {
    self.lock().unwrap().mk( App(id, args) )
  }
}

pub trait BindMaker<Trm> {
  fn forall(& self, Vec<id::Id>, Trm) -> Term ;
  fn exists(& self, Vec<id::Id>, Trm) -> Term ;
  fn let_b(& self, Vec<(id::Id, Term)>, Trm) -> Term ;
}
impl<
  'a, Trm: Clone, T: Sized + BindMaker<Trm>
> BindMaker<& 'a Trm> for T {
  fn forall(& self, bind: Vec<id::Id>, term: & 'a Trm) -> Term {
    self.forall( bind, term.clone() )
  }
  fn exists(& self, bind: Vec<id::Id>, term: & 'a Trm) -> Term {
    self.exists( bind, term.clone() )
  }
  fn let_b(& self, bind: Vec<(id::Id, Term)>, term: & 'a Trm) -> Term {
    self.let_b( bind, term.clone() )
  }
}
impl BindMaker<Term> for TermConsign {
  fn forall(& self, bind: Vec<id::Id>, term: Term) -> Term {
    self.lock().unwrap().mk( Forall(bind, term) )
  }
  fn exists(& self, bind: Vec<id::Id>, term: Term) -> Term {
    self.lock().unwrap().mk( Exists(bind, term) )
  }
  fn let_b(& self, bind: Vec<(id::Id, Term)>, term: Term) -> Term {
    self.lock().unwrap().mk( Let(bind, term) )
  }
}