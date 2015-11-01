// Copyright 2015 Adrien Champion. See the COPYRIGHT file at the top-level
// directory of this distribution.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

/*! Variables, stateful and non-stateful. */

use std::io ;

use base::{
  State, Writable, SVarWriter, StateWritable, SymPrintStyle, SymWritable,
  HConsed, HConsign
} ;
use sym::Sym ;

/** Underlying representation of variables. */
#[derive(Debug,Clone,PartialEq,Eq,PartialOrd,Ord,Hash)]
pub enum RealVar {
  /** Non-stateful variable. */
  Var(Sym),
  /** Stateful variable. */
  SVar(Sym, State),
}

/** Hash consed variable. */
pub type Var = HConsed<RealVar> ;

impl<Svw: SVarWriter<Sym>> StateWritable<Sym, Svw> for Var {
  #[inline(always)]
  fn write(
    & self, writer: & mut io::Write, sv_writer: & Svw, style: SymPrintStyle
  ) -> io::Result<()> {
    match * self.get() {
      RealVar::Var(ref sym) => {
        try!( write!(writer, "|") ) ;
        try!( sym.write(writer, style) ) ;
        write!(writer, "|")
      },
      RealVar::SVar(ref sym, ref st) =>
        sv_writer.write(writer, sym, st, style),
    }
  }
}

/** Hash cons table for variables. */
pub type VarConsign = HConsign<RealVar> ;

/** Can create non-stateful stateful variables. */
pub trait VarMaker<Symbol, Out> {
  /** Creates a non-stateful variable. */
  #[inline]
  fn var(& self, Symbol) -> Out ;
  /** Creates a stateful variable. */
  #[inline]
  fn svar(& self, Symbol, State) -> Out ;
}
impl VarMaker<Sym,Var> for VarConsign {
  fn var(& self, id: Sym) -> Var {
    self.lock().unwrap().mk( RealVar::Var(id) )
  }
  fn svar(& self, id: Sym, state: State) -> Var {
    self.lock().unwrap().mk( RealVar::SVar(id, state) )
  }
}


