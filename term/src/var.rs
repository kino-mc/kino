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
use std::fmt ;

use base::{
  State, SVarWriter, StateWritable, SymPrintStyle, SymWritable,
  HConsed, HConsign, HConser
} ;
use sym::Sym ;

/// Underlying representation of variables.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum RealVar {
  /// Non-stateful variable.
  Var(Sym),
  /// Stateful variable.
  SVar(Sym, State),
}
impl RealVar {
  /// The state of variable.
  #[inline]
  pub fn state(& self) -> Option<State> {
    match * self {
      RealVar::SVar(_, ref state) => Some(* state),
      _ => None,
    }
  }

  /// Bumps a variable in the current state to the next state.
  #[inline(always)]
  pub fn bump(& self) -> Result<Self,bool> {
    match * self {
      RealVar::SVar(ref sym, State::Curr) => Ok(
        RealVar::SVar( sym.clone(), State::Next )
      ),
      RealVar::SVar(_,_) => Err(true),
      _ => Err(false),
    }
  }

  /// The symbol stored in a variable.
  #[inline(always)]
  pub fn sym(& self) -> & Sym {
    match * self {
      RealVar::Var(ref sym) => sym,
      RealVar::SVar(ref sym, _) => sym,
    }
  }
}

impl fmt::Display for RealVar {
  fn fmt(& self, fmt: & mut fmt::Formatter) -> fmt::Result {
    match * self {
      RealVar::Var(ref s) => write!(fmt, "|{}|", s.get().sym()),
      RealVar::SVar(ref s, State::Curr) => write!(
        fmt, "(_ state |{}|)", s.get().sym()
      ),
      RealVar::SVar(ref s, State::Next) => write!(
        fmt, "(_ next |{}|)", s.get().sym()
      ),
    }
  }
}

/// Hash consed variable.
pub type Var = HConsed<RealVar> ;

impl<Svw: SVarWriter<Sym>> StateWritable<Sym, Svw> for RealVar {
  #[inline(always)]
  fn write(
    & self, writer: & mut io::Write, sv_writer: & Svw, style: SymPrintStyle
  ) -> io::Result<()> {
    match * self {
      RealVar::Var(ref sym) => {
        try!( write!(writer, "|") ) ;
        try!( sym.write(writer, style) ) ;
        write!(writer, "|")
      },
      RealVar::SVar(ref sym, ref st) =>
        sv_writer.sv_write(writer, sym, st, style),
    }
  }
}

impl<Svw: SVarWriter<Sym>> StateWritable<Sym, Svw> for Var {
  #[inline(always)]
  fn write(
    & self, writer: & mut io::Write, sv_writer: & Svw, style: SymPrintStyle
  ) -> io::Result<()> {
    self.get().write(writer, sv_writer, style)
  }
}

/// Hash cons table for variables.
pub type VarConsign = HConsign<RealVar> ;

/// Can create non-stateful stateful variables.
pub trait VarMaker<Symbol, Out> {
  /// Creates a non-stateful variable.
  #[inline]
  fn var(& self, Symbol) -> Out ;
  /// Creates a stateful variable.
  #[inline]
  fn svar(& self, Symbol, State) -> Out ;
}
impl VarMaker<Sym,Var> for VarConsign {
  fn var(& self, id: Sym) -> Var {
    self.mk( RealVar::Var(id) )
  }
  fn svar(& self, id: Sym, state: State) -> Var {
    self.mk( RealVar::SVar(id, state) )
  }
}


