// Copyright 2015 Adrien Champion. See the COPYRIGHT file at the top-level
// directory of this distribution.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

/*! Terms for kinō.

Real, underlying structures are in module `real`.
Function symbols (`Sym`), constants (`Cst`) and terms (`Term`) are hash consed
for perfect/maximal **and concurrent** sharing.

In the following STS stands for the *SMT Lib Transition System* Standard as
defined in `panic!("undefined")`.

## Handling the state

Terms can have non-stateful variables or stateful variables. Stateful
variables can be either in

* the current state ([`State`][state]`::Curr`), or
* the next state ([`State`][state]`::Next`).

**For SMT Lib 2** the offset of state-variables (*i.e.* unrolling) is given
when printing terms. For more details, see

* trait [`PrintSmt2`][print smt 2] for printing, and
* struct [`Offset2`][offset2] to specify the offset.


## SMT naming convention

A state variable `<var>` unrolled at `7` is understood printing/parsing-wise
as `|@7 <var>|`. A non-stateful variable `<var>` is printed as `| <var>|`.
This way, a symbol `@42 my_var` will is printed as `| @42 my_var|`. It cannot
be mistaken for a stateful variable `|@42 my_var|`.

So at SMT level all symbols have the shape
`"|" ~ opt("@<int>") ~ " " ~ "<id>" ~ "|"`

## STS naming convention

Printing and parsing in STS works as expected, except that printing always
prints symbols as quoted symbols.

## Parsing

Parsing STS and parsing answers in SMT Lib is different.

* STS is standardized and do not have offsets *per se*. Stateful variables
  are specified with

  *  `(state <my_var>)` to refer to `<my_var>` in the current state, and
  *  `(next  <my_var>)` to refer to `<my_var>` in the next state.

* SMT Lib 2 terms can have arbitrary offsets because when doing a `get-value`
  or a `get-model`, the unrolling will *a priori* mess up the current/next
  convention for terms.
  This is why the [SMT Lib 2 parsing][parse smt 2] trait implementation for
  expressions in [Factory][factory] returns a variable and an
  [`Offset`][offset] option.

## TODO

* [`StateWritable::write`][state writable] for terms copies way too much stuff
* `num::rational` crash if denominator is zero. Can happen in parser. Parsing
only non-zero denominator will push the problem to function symbol application. Need proper handling.
* document [`write` module][write module]


[state]: enum.State.html (State enum type)
[print smt 2]: trait.PrintSmt2.html (PrintSmt2 trait)
[factory]: struct.Factory.html (Term factory struct)
[offset]: struct.Offset.html (Offset struct)
[offset2]: struct.Offset2.html (Offset2 struct)
[smt 2 offset]: enum.Smt2Offset.html (Smt2Offset struct)
[parse smt 2]: trait.ParseSmt2.html (ParseSmt2 trait)
[state writable]: write/trait.StateWritable.html (StateWritable trait)
[write module]: write/index.html (write module)
*/

extern crate num ;
#[macro_use]
extern crate nom ;
extern crate hashconsing as hcons ;
extern crate rsmt2 ;

macro_rules! unimpl {
  () => ( panic!("not implemented") ) ;
}

mod base ;
pub use base::{
  State, PrintSmt2, PrintSts2, Offset, Offset2, Smt2Offset
} ;
mod typ ;
pub use typ::{ Type, Bool, Int, Rat } ;
mod sym ;
pub use sym::{ Sym, SymMaker } ;
mod cst ;
pub use cst::{ Cst } ;
mod var ;
pub use var::{ Var, VarMaker } ;
mod term ;
pub use term::{
  Operator, Term, CstMaker, OpMaker, BindMaker, AppMaker
} ;
mod parser ;
pub use parser::sts2::TermAndDep ;
mod factory ;
pub use factory::{ Factory, ParseSts2, UnTermOps } ;

/** Real, underlying representation of symbols, constants and terms. */
pub mod real {
  pub use sym::RealSym as Sym ;
  pub use var::RealVar as Var ;
  pub use cst::RealCst as Cst ;
  pub use term::RealTerm as Term ;
}

/** Internal traits used for SMT Lib 2 and STS Lib 2 writing.

Exposed for extensibility. */
pub mod write {
  pub use base::{ Writable, SVarWriter, StateWritable } ;
}

/** SMT solver. */
pub mod smt {
  use ::std::process::Command ;

  use ::rsmt2::{ Sort2Smt, Sym2Smt, Expr2Smt } ;

  /** Wraps an SMT solver. */
  pub type Solver = ::rsmt2::Solver<::Factory> ;
  #[inline(always)]
  pub fn z3_cmd() -> Command { Command::new("z3") } 
  pub use ::rsmt2::{ SolverConf } ;

  pub use ::rsmt2::sync ;
  pub use ::rsmt2::async ;

  impl Sym2Smt for ::real::Sym {
    fn sym_to_smt2(
      & self, writer: & mut ::std::io::Write
    ) -> ::std::io::Result<()> {
      write!(writer, "{}", self)
    }
  }

  impl Sort2Smt for ::Type {
    fn sort_to_smt2(
      & self, writer: & mut ::std::io::Write
    ) -> ::std::io::Result<()> {
      use base::Writable ;
      self.write(writer)
    }
  }

  /** An unrolled term, printable in a solver. */
  pub struct Unroll(::Term, ::Offset2) ;
  impl Expr2Smt for Unroll {
    fn expr_to_smt2(
      & self, writer: & mut ::std::io::Write
    ) -> ::std::io::Result<()> {
      use base::PrintSmt2 ;
      let Unroll(ref term, ref offset) = * self ;
      term.to_smt2(writer, offset)
    }
  }
}