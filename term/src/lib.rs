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
defined in `panic!(undefined)`.

## Handling the state

Terms can have non-stateful variables or stateful variables. Stateful
variables can be either in

* the current state ([`State`][state]`::Curr`), or
* the next state ([`State`][state]`::Next`).

**In SMT Lib 2** the offset of state-variables (*i.e.* unrolling) is given
when printing. For more details, see

* trait [`PrintSmt2`][print smt 2] for printing, and
* struct [`Smt2Offset`][smt 2 offset] to specify the offset.


## Conventions *when interacting with SMT-solvers*

A state variable `<var>` unrolled at `7` is understood printing/parsing-wise
as `|@7<var>|`. This can be ambiguous depending on how the variables are
sanitized in the STS frontend.

The guideline is that when parsing STS, a variable `<var>` should be sanitized
as a function symbol `| <var>|`. This way, a variable declared in a STS as
`@42my_var` will be sanitized as `| @42my_var|`. It cannot be mistaken for a
stateful variable `|@42my_var|` SMT-Lib-2-wise.




## Parsing

Parsing is different when parsing STS versus parsing answers in SMT Lib.

* STS is standardized and do not have offsets *per say*. Stateful variables
  are specified with

  *  `(state <my_var>)` to refer to `<my_var>` in the current state, and
  *  `(next  <my_var>)` to refer to `<my_var>` in the next state.

* SMT Lib 2 terms can have arbitrary offsets because when doing a `get-value`
  or a `get-model`, the unrolling will *a priori* mess up the current/next
  convention for terms.
  This is why the [SMT Lib 2 parsing][parse smt 2] trait implementation for
  expressions in [Factory][factory] returns a term and an
  [`Smt2Offset`][smt 2 offset].

## TODO

* `num::rational` crash if denominator is zero. Can happen in parser. Parsing
only non-zero denominator will push the problem to function symbol application. Need proper handling.
* `PrintSmt2::to_smt2` for terms copies way too much stuff


[state]: enum.State.html (State enum type)
[print smt 2]: trait.PrintSmt2.html (PrintSmt2 trait)
[factory]: struct.Factory.html (Term factory struct)
[smt 2 offset]: struct.Offset2.html (Offset2 struct)
[parse smt 2]: trait.ParseSmt2.html (ParseSmt2 trait)
*/

extern crate num ;
#[macro_use]
extern crate nom ;
extern crate hashconsing as hcons ;
extern crate rsmt2 as smt ;
pub use smt::ParseSmt2 ;

macro_rules! unimpl {
  () => ( panic!("not implemented") ) ;
}

mod base ;
pub use base::{
  State, PrintSmt2, Offset, Offset2, Smt2Offset
} ;
mod typ ;
pub use typ::{ Type, Bool, Int, Rat } ;
mod sym ;
pub use sym::{ Sym, SymMaker } ;
mod cst ;
pub use cst::{ Cst } ;
mod term ;
pub use term::{
  Term, VarMaker, CstMaker, OpMaker, BindMaker, AppMaker, UnTermOps
} ;
mod parser ;
mod factory ;
pub use factory::{ Factory, ParseSts2 } ;

/** Real, underlying representation of symbols, constants and terms. */
pub mod real {
  pub use sym::RealSym as Sym ;
  pub use cst::RealCst as Cst ;
  pub use term::RealTerm as Term ;
}