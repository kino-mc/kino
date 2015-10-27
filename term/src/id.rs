/** Identifiers structures and parsers. */

use ::base::* ;
use ::sym::* ;

#[derive(PartialEq,Eq,PartialOrd,Ord,Hash)]
pub struct Identifier {
  sym: Sym
}

pub type Id = HConsed<Identifier> ;

pub type IdConsign = HConsign<Identifier> ;

pub trait IdFactory {
  fn of_sym(& self, sym: Sym) -> Id ;
}

impl IdFactory for IdConsign {
  fn of_sym(& self, sym: Sym) -> Id {
    self.lock().unwrap().mk( Identifier { sym: sym } )
  }
}