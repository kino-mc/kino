#![deny(missing_docs)]
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

In the following TSV stands for the *SMT Lib Transition System* Standard as
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

## TSV naming convention

Printing and parsing in TSV works as expected, except that printing always
prints symbols as quoted symbols.

## Parsing

Parsing TSV and parsing answers in SMT Lib is different.

* TSV is standardized and do not have offsets *per se*. Stateful variables
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

* modify rsmt2 so that `get_model` returns a hashmap
* [`StateWritable::write`][state writable] for terms copies way too much stuff
* `num::rational` crash if denominator is zero. Can happen in parser. Parsing
only non-zero denominator will push the problem to function symbol application. Need proper handling.
* document [`write` module][write module]
* provide local fresh symbol constructor
* have separate enum for actlits (print as `|@actlit <num>|`)
* factor type checking code for operators


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
extern crate error_chain ;
#[macro_use]
extern crate nom ;
extern crate rand ;
extern crate hashconsing as hcons ;
#[macro_use]
extern crate rsmt2 ;

use std::collections::{ HashSet, HashMap } ;

macro_rules! unimpl {
  () => ( panic!("not implemented") ) ;
}

pub use nom::{ IResult } ;

/// Re-export of `rsmt2`'s errors.
pub mod errors {
  error_chain!{
    types {
      Error, ErrorKind, ResExt, Res ;
    }
    links {
      RSmt2(::rsmt2::errors::Error, ::rsmt2::errors::ErrorKind)
      #[doc = "[`rsmt2`](https://crates.io/crates/rsmt2) errors"] ;
    }
    errors {
      #[doc = "Returned when a term evaluation fails."]
      EvalError(s: String) {
        description("evaluation error")
        display("evaluation error: {}", s)
      }

      #[doc = "
        Returned when a temp term transformation fails.
      "]
      TmpTransError {
        description("temp term transformation error")
        display("temp term transformation error")
      }

      #[doc = "Operator arity mismatch."]
      OpArityError(op: ::Operator, found: usize, expected: & 'static str) {
        description("operator arity mismatch")
        display(
          "arity mismatch, operator `{}` applied to {} operands (expected {})",
          op, found, expected
        )
      }

      #[doc = "Type mismatch on operator."]
      OpTypeError(
        op: ::Operator, found: ::Type, expected: ::Type, blah: Option<String>
      ) {
        description("operator type mismatch")
        display(
          "type mismatch on operator `{}`, expected {} but found {}{}",
          op, expected, found, match * blah {
            Some(ref blah) => format!(" {}", blah),
            None => "".into(),
          }
        )
      }

      #[doc = "IO error"]
      IoError(e: ::std::io::Error) {
        description("IO error")
        display("IO error {:?}", e)
      }
    }
  }
}

mod base ;
pub use base::{
  State, PrintSmt2, PrintVmt, Offset, Offset2, Smt2Offset
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
  Operator, Term, STerm, CstMaker, BindMaker, AppMaker, OpMaker
} ;
pub mod tmp ;
#[macro_use]
mod parser ;
/// Parsing stuff.
pub mod parsing {
  pub use super::parser::vmt::TermAndDep ;
  pub use super::parser::{ Span, Spanned, Bytes } ;
}
mod factory ;
pub use factory::{ Factory, ParseVmt2, UnTermOps } ;
pub mod gen ;

/// A model is a vector of variables with optional offset and values.
pub type Model = Vec<( (Var, Option<Offset>), Cst )> ;

/// A set of constants.
pub type CstSet = HashSet<Cst> ;
/// A set of variables.
pub type VarSet = HashSet<Var> ;
/// A set of terms.
pub type TermSet = HashSet<Term> ;
/// A map from terms to something.
pub type TermMap<Val> = HashMap<Term, Val> ;
/// A set of state terms.
pub type STermSet = HashSet<STerm> ;
/// A map from state terms to something.
pub type STermMap<Val> = HashMap<STerm, Val> ;

/// Real, underlying representation of symbols, constants and terms.
pub mod real_term {
  pub use sym::RealSym as Sym ;
  pub use var::RealVar as Var ;
  pub use cst::RealCst as Cst ;
  pub use term::RealTerm as Term ;
}

/// Zipper on terms.
pub mod zip {
  pub use term::zip2::{ Step, fold, fold_info, extract } ;
}

/// Internal traits used for SMT Lib 2 and TSV Lib 2 writing.
///
/// Exposed for extensibility.
pub mod write {
  pub use base::{ Writable, SVarWriter, StateWritable } ;
}

// Re-export of num.
pub use ::num::* ;

/// SMT solver.
pub mod smt {
  use ::std::process::Command ;

  pub use ::rsmt2::* ;
  use ::rsmt2::errors::* ;

  /// The default z3 command.
  #[inline(always)]
  pub fn z3_cmd() -> Command { Command::new("z3") }
  /// The default cvc4 command.
  #[inline(always)]
  pub fn cvc4_cmd() -> Command { Command::new("cvc4") }

  impl Sym2Smt<::Offset> for ::Sym {
    fn sym_to_smt2(
      & self, writer: & mut ::std::io::Write, _: & ::Offset
    ) -> Res<()> {
      use base::SymWritable ;
      use base::SymPrintStyle ;
      smt_cast_io!(
        format!("writing symbol `{}`", self) =>
          write!(writer, "|") ;
          self.write(writer, SymPrintStyle::Internal) ;
          write!(writer, "|")
      )
    }
  }

  impl Sym2Smt<::Offset2> for ::Sym {
    fn sym_to_smt2(
      & self, writer: & mut ::std::io::Write, _: & ::Offset2
    ) -> Res<()> {
      use base::SymWritable ;
      use base::SymPrintStyle ;
      smt_cast_io!(
        format!("writing symbol `{}`", self) =>
          write!(writer, "|") ;
          self.write(writer, SymPrintStyle::Internal) ;
          write!(writer, "|")
      )
    }
  }

  impl Sym2Smt<::Offset> for ::Var {
    fn sym_to_smt2(
      & self, writer: & mut ::std::io::Write, info: & ::Offset
    ) -> Res<()> {
      use base::StateWritable ;
      use base::SymPrintStyle ;
      smt_cast_io!(
        format!(
          "writing symbol `{}` with offset `{}`", self, info
        ) => self.write(
          writer, info, SymPrintStyle::Internal
        )
      )
    }
  }

  impl Sym2Smt<::Offset2> for ::Var {
    fn sym_to_smt2(
      & self, writer: & mut ::std::io::Write, info: & ::Offset2
    ) -> Res<()> {
      use base::StateWritable ;
      use base::SymPrintStyle ;
      smt_cast_io!(
        format!(
          "writing symbol `{}` with offset `{}`", self, info
        ) => self.write(
          writer, info, SymPrintStyle::Internal
        )
      )
    }
  }

  impl Expr2Smt<::Offset2> for ::Term {
    fn expr_to_smt2(
      & self, writer: & mut ::std::io::Write, offset: & ::Offset2
    ) -> Res<()> {
      use base::PrintSmt2 ;
      smt_cast_io!(
        format!("writing `{}` with offset `{}`", self, offset) => self.to_smt2(
          writer, offset
        )
      )
    }
  }

  impl Sort2Smt for ::Type {
    fn sort_to_smt2(
      & self, writer: & mut ::std::io::Write
    ) -> Res<()> {
      use base::Writable ;
      smt_cast_io!(
        format!("writing sort `{}`", self) => self.write(writer)
      )
    }
  }
}
