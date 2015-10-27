/*! Symbol-related structures and parsers. */

use ::base::* ;

#[derive(PartialEq,Eq,PartialOrd,Ord,Hash)]
pub struct Symbol {
  sym: String
}

pub type Sym = HConsed<Symbol> ;

pub type SymConsign = HConsign<Symbol> ;

pub trait SymFactory {
  fn of_str(& self, & str) -> Sym ;
  fn of_string(& self, String) -> Sym ;
}

impl SymFactory for SymConsign {
  fn of_str(& self, sym: & str) -> Sym {
    self.lock().unwrap().mk( Symbol { sym: sym.to_string() } )
  }
  fn of_string(& self, sym: String) -> Sym {
    self.lock().unwrap().mk( Symbol { sym: sym } )
  }
}