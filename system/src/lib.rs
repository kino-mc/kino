#![allow(non_upper_case_globals)]
#![deny(missing_docs)]
// Copyright 2015 Adrien Champion. See the COPYRIGHT file at the top-level
// directory of this distribution.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

/*! Transition system library.

## Hash consing

[`Sym`][sym type] and [`Term`][term type] come from the kinō
[`term`][term crate] crate and are hash consed. Remember that one should
**never** create more that one [Factory][factory struct] for these. It is
thread-safe and can be cloned.

[`Context`][context struct] holds one for parsing.

## Thread-safety

All constructions related to systems (`Sys`, `Prop`, `Args`, *etc.*) are
wrapped in an `Arc` and thus are thread-safe.

## To do

* more clever input consumption in [`Context`][context struct]
* less copy in [`Context`][context struct]
* more informative parse error (depency checking)
* spanned parse errors
* integrate type checking in parser
* support for `stdin`-like input

[sym type]: ../term/type.Sym.html (Sym type)
[term type]: ../term/type.Term.html (Term type)
[term crate]: ../term/index.html (term crate)
[factory struct]: ../term/struct.Factory.html (Factory struct)
[context struct]: ctxt/struct.Context.html (Context struct)
*/


#[macro_use]
extern crate nom ;
#[macro_use]
extern crate error_chain ;
#[macro_use]
extern crate term ;

use std::sync::Arc ;
use std::fmt ;

/// A line with a line number, a sub line indicating something in the line,
/// and a column number.
#[derive(Debug)]
pub struct Line {
  /// The line.
  pub line: String,
  /// The subline showing something in the line above.
  pub subline: String,
  /// The line number of the line.
  pub l: usize,
  /// The column of the token of interest in the line.
  pub c: usize,
}
impl Line {
  /// Creates a line.
  #[inline]
  pub fn mk(line: String, subline: String, l: usize, c: usize) -> Self {
    Line { line: line, subline: subline, l: l, c: c }
  }
}
impl fmt::Display for Line {
  fn fmt(& self, fmt: & mut fmt::Formatter) -> fmt::Result {
    write!(fmt, "[{}:{}] `{}`", self.line, self.l, self.c)
  }
}

/// Errors.
#[derive(Debug)]
pub enum Error {
  /// Parse error.
  Parse {
    /// Line of the error.
    line: Line,
    /// Description of the error.
    blah: String,
    /// Optional notes about the error.
    notes: Vec<(Line, String)>
  },
  /// IO error.
  Io(::std::io::Error)
}
impl Error {
  /// Creates a parsing error.
  #[inline]
  pub fn parse_mk(
    line: Line, blah: String, notes: Vec<(Line, String)>
  ) -> Self {
    Error::Parse { line: line, blah: blah, notes: notes }
  }

  /// Prints an internal parse error.
  #[cfg(test)]
  pub fn print(& self) {
    match * self {
      Error::Parse { ref line, ref blah, ref notes } => {
        println!("parse error {}: {}", line, blah) ;
        for & (ref line, ref blah) in notes {
          println!("| {}: {}", line, blah)
        }
      },
      Error::Io(ref e) => println!("io error: {:?}", e)
    }
  }
}
impl fmt::Display for Error {
  fn fmt(& self, fmt: & mut fmt::Formatter) -> fmt::Result {
    match * self {
      Error::Parse { ref line, ref blah, .. } => write!(
        fmt, "{} in line {}", blah, line
      ),
      Error::Io(ref e) => write!(fmt, "io error: {:?}", e),
    }
  }
}

mod base ;
mod type_check ;
mod parse ;

/// Real types of the elements of a context.
pub mod real_sys {
  pub use base::{
    Sig, Args, Uf, Fun, Prop, Sys, Callable
  } ;
}

/// Parses, type checks and remembers the input.
pub mod ctxt {
  pub use super::base::Callable ;
  pub use super::parse::{
    Res, Context
  } ;
  pub use super::parse::check::CheckError ;
  pub use type_check::type_check ;
}

pub use base::{ CallSet, PropStatus } ;

pub use parse::Cex ;

/// A signature, a list of types. Used only in `Uf`.
pub type Sig = Arc<base::Sig> ;
/// A list of typed formal parameters.
pub type Args = Arc<base::Args> ;
/// An uninterpreted function.
pub type Uf = Arc<base::Uf> ;
/// A function (actually a macro in SMT-LIB).
pub type Fun = Arc<base::Fun> ;
/// Wraps an (uninterpreted) function.
pub type Callable = Arc<base::Callable> ;
/// A property.
pub type Prop = Arc<base::Prop> ;
/// A transition system.
pub type Sys = Arc<base::Sys> ;


