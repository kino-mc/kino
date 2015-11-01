/*! Function symbols. */

use std::io ;

use base::{ PrintSmt2, Offset2, HConsed, HConsign } ;


/** Underlying representation for function symbols. */
#[derive(Debug,PartialEq,Eq,PartialOrd,Ord,Hash)]
pub struct RealSym {
  /** The `String` representing the function symbol. */
  sym: String
}

/** Hash consed function symbol. */
pub type Sym = HConsed<RealSym> ;

impl PrintSmt2 for Sym {
  #[inline(always)]
  fn to_smt2(& self, writer: & mut io::Write, _: & Offset2) -> io::Result<()> {
    write!(writer, "{}", self.get().sym)
  }
}

/** Hash cons table for function symbols. */
pub type SymConsign = HConsign<RealSym> ;

/** Can create a function symbol. */
pub trait SymMaker<T> {
  /** Creates a function symbol. */
  #[inline(always)]
  fn sym(& self, T) -> Sym ;
}

impl SymMaker<String> for SymConsign {
  fn sym(& self, sym: String) -> Sym {
    self.lock().unwrap().mk( RealSym { sym: sym } )
  }
}
impl<'a> SymMaker<& 'a str> for SymConsign {
  fn sym(& self, sym: & 'a str) -> Sym {
    self.lock().unwrap().mk( RealSym { sym: sym.to_string() } )
  }
}