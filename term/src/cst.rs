/** Constant structures. */

use ::base::* ;
use ::typ ;

use self::Constant::* ;

#[derive(Debug,Clone,PartialEq,Eq,PartialOrd,Ord,Hash)]
pub enum Constant {
  Bool(typ::Bool),
  Int(typ::Int),
  Rat(typ::Rat),
}

pub type Cst = HConsed<Constant> ;
pub type CstConsign = HConsign<Constant> ;

pub trait CstMaker<Const> {
  fn cst(& self, Const) -> Cst ;
}
impl<
  'a, Const: Clone, T: Sized + CstMaker<Const>
> CstMaker<& 'a Const> for T {
  fn cst(& self, cst: & 'a Const) -> Cst {
    (self as & CstMaker<Const>).cst(cst.clone())
  }
}
impl CstMaker<typ::Bool> for CstConsign {
  fn cst(& self, b: typ::Bool) -> Cst {
    self.lock().unwrap().mk( Bool(b) )
  }
}
impl CstMaker<typ::Int> for CstConsign {
  fn cst(& self, i: typ::Int) -> Cst {
    self.lock().unwrap().mk( Int(i) )
  }
}
impl CstMaker<typ::Rat> for CstConsign {
  fn cst(& self, r: typ::Rat) -> Cst {
    self.lock().unwrap().mk( Rat(r) )
  }
}
