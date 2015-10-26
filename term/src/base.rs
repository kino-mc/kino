/*! Basic traits and structures. */

pub use hcons::* ;

pub use std::sync::{ Arc, Mutex } ;

/** Under the hood an offset is a `u16`. */
pub type Offset = u16 ;

/** One-state offset. */
pub struct Offset1(Offset) ;

/** Two-state offset.

First is current step, second is next. */
pub struct Offset2(Offset, Offset) ;




pub type HConsign<T> = Arc<Mutex<HashConsign<T>>> ;


pub mod typ {
  pub trait Type {}

  pub type Bool = bool ;
  impl Type for Bool {}

  pub type Int = ::num::BigInt ;
  impl Type for Int {}

  pub type Rat = ::num::rational::BigRational ;
  impl Type for Rat {}
}


// pub mod cst {
//   use super::* ;
//   use super::typ::* ;
//   use self::Constant::* ;

//   #[derive(PartialEq,Eq,PartialOrd,Ord,Hash)]
//   pub enum Constant {
//     B(Bool),
//     I(Int),
//     R(Rat),
//   }

//   pub type Const = HConsed<Constant> ;

//   pub type ConstConsign = HConsign<Constant> ;

//   pub trait ConstFactory {
//     fn of_bool(& self, b: Bool) -> Const ;
//     fn of_int(& self, b: Int) -> Const ;
//     fn of_rat(& self, b: Rat) -> Const ;
//   }

//   impl ConstFactory for ConstConsign {
//     fn of_bool(& self, b: Bool) -> Const {
//       self.lock().unwrap().mk( B(b) )
//     }
//     fn of_int(& self, i: Int) -> Const {
//       self.lock().unwrap().mk( I(i) )
//     }
//     fn of_rat(& self, r: Rat) -> Const {
//       self.lock().unwrap().mk( R(r) )
//     }
//   }
// }

pub mod sym {
  use super::* ;

  #[derive(PartialEq,Eq,PartialOrd,Ord,Hash)]
  pub struct Symbol {
    sym: String
  }

  pub type Sym = HConsed<Symbol> ;

  pub type SymConsign = HConsign<Symbol> ;

  pub trait SymFactory {
    fn of_str(& self, sym: & str) -> Sym ;
  }

  impl SymFactory for SymConsign {
    fn of_str(& self, sym: & str) -> Sym {
      self.lock().unwrap().mk( Symbol { sym: sym.to_string() } )
    }
  }
}


pub mod id {
  use super::* ;

  #[derive(PartialEq,Eq,PartialOrd,Ord,Hash)]
  pub struct Identifier {
    sym: sym::Sym
  }

  pub type Id = HConsed<Identifier> ;

  pub type IdConsign = HConsign<Identifier> ;

  pub trait IdFactory {
    fn of_sym(& self, sym: sym::Sym) -> Id ;
  }

  impl IdFactory for IdConsign {
    fn of_sym(& self, sym: sym::Sym) -> Id {
      self.lock().unwrap().mk( Identifier { sym: sym } )
    }
  }
}

// pub mod var {
//   use super::* ;
//   use self::Variable::* ;

//   #[derive(PartialEq,Eq,PartialOrd,Ord,Hash)]
//   pub enum Variable {
//     NSVar(id::Id),
//     SVar0(id::Id),
//     SVar1(id::Id),
//   }

//   pub type Var = HConsed<Variable> ;

//   pub type VarConsign = HConsign<Variable> ;

//   pub trait VarFactory {
//     fn nsvar(& self, id: id::Id) -> Var ;
//     fn svar0(& self, id: id::Id) -> Var ;
//     fn svar1(& self, id: id::Id) -> Var ;
//   }

//   impl VarFactory for VarConsign {
//     fn nsvar(& self, id: id::Id) -> Var {
//       self.lock().unwrap().mk( NSVar(id) )
//     }
//     fn svar0(& self, id: id::Id) -> Var {
//       self.lock().unwrap().mk( SVar0(id) )
//     }
//     fn svar1(& self, id: id::Id) -> Var {
//       self.lock().unwrap().mk( SVar1(id) )
//     }
//   }
// }

pub mod term {
  use super::* ;
  use self::TerM::* ;

  #[derive(PartialEq,Eq,PartialOrd,Ord,Hash)]
  pub enum TerM {
    Var(id::Id),
    SVar0(id::Id),
    SVar1(id::Id),
    Bool(typ::Bool),
    Int(typ::Int),
    Rat(typ::Rat),
    App(id::Id, Vec<Term>),
  }

  pub type Term = HConsed<TerM> ;
  pub type TermConsign = HConsign<TerM> ;

  pub trait VarMaker<Id> {
    fn var(& self, Id) -> Term ;
    fn svar0(& self, Id) -> Term ;
    fn svar1(& self, Id) -> Term ;
  }
  impl<
    'a, Id: Clone, T: Sized + VarMaker<Id>
  > VarMaker<& 'a Id> for T {
    fn var(& self, id: & 'a Id) -> Term {
      (self as & VarMaker<Id>).var(id.clone())
    }
    fn svar0(& self, id: & 'a Id) -> Term {
      (self as & VarMaker<Id>).svar0(id.clone())
    }
    fn svar1(& self, id: & 'a Id) -> Term {
      (self as & VarMaker<Id>).svar1(id.clone())
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

  impl VarMaker<id::Id> for TermConsign {
    fn var(& self, id: id::Id) -> Term {
      self.lock().unwrap().mk( Var(id) )
    }
    fn svar0(& self, id: id::Id) -> Term {
      self.lock().unwrap().mk( SVar0(id) )
    }
    fn svar1(& self, id: id::Id) -> Term {
      self.lock().unwrap().mk( SVar1(id) )
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

  impl AppMaker<id::Id> for TermConsign {
    fn app(& self, id: id::Id, args: Vec<Term>) -> Term {
      self.lock().unwrap().mk( App(id, args) )
    }
  }
}