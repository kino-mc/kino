// Copyright 2015 Adrien Champion. See the COPYRIGHT file at the top-level
// directory of this distribution.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

/*! Basic traits and structures. */

use std::io ;
use std::fmt ;
use std::hash::Hash ;
use std::sync::{ Arc, Mutex } ;

pub use hcons::* ;

#[derive(Clone,Copy)]
/** Decides how symbols are printed. */
pub enum SymPrintStyle {
  /** Internal print style adds a ' ' before the symbol is printed. */
  Internal,
  /** External is printing the symbol as it is. */
  External,
}

/** A state is either current or next. */
#[derive(Debug,Clone,Copy,PartialEq,Eq,PartialOrd,Ord,Hash)]
pub enum State {
  /** Current state. */
  Curr,
  /** Next state. */
  Next,
}

/** Printable in the STS 2 standard. */
pub trait PrintSts2 {
  /** Prints something in STS 2 in a `Write`. */
  fn to_sts2(& self, & mut io::Write) -> io::Result<()> ;
}

/** Printable in the SMT Lib 2 standard, given an offset. */
pub trait PrintSmt2 {
  /** Prints something in SMT Lib 2 in a `Write`, given an offset. */
  fn to_smt2(& self, & mut io::Write, & Offset2) -> io::Result<()> ;
}

/** Can write itself. */
pub trait Writable {
  /** Writes itself. */
  fn write(& self, & mut io::Write) -> io::Result<()> ;
}

/** Can write itself as a symbol. */
pub trait SymWritable {
  /** Writes itself given a print style. */
  fn write(& self, & mut io::Write, SymPrintStyle) -> io::Result<()> ;
}

/** Can write a state variable given a state. */
pub trait SVarWriter<Sym: SymWritable> {
  /** Writes a state variable given a state. */
  #[inline(always)]
  fn sv_write(
    & self, & mut io::Write, & Sym, & State, SymPrintStyle
  ) -> io::Result<()> ;
}

/** Can write itself given a state writer and a print style. */
pub trait StateWritable<S: SymWritable, Svw: SVarWriter<S>> {
  /** Writes itself given a state writer and a print style. */
  fn write(& self, & mut io::Write, & Svw, SymPrintStyle) -> io::Result<()> ;
}

/** An offset. */
#[derive(Debug,PartialEq,Eq,PartialOrd,Ord,Hash,Clone,Copy)]
pub struct Offset { offset: u16 }

impl Offset {
  /** Bytes to Offset conversion. */
  pub fn of_bytes(bytes: & [u8]) -> Self {
    // -> Result<Offset, std::num::ParseIntError> {
    use std::str ;
    Offset {
      offset: u16::from_str_radix(
        str::from_utf8(bytes).unwrap(), 10
      ).unwrap()
    }
  }

  /** `usize` to Offset conversion. */
  pub fn of_int(int: usize) -> Self {
    Offset {
      offset: u16::from_str_radix(
        & int.to_string(), 10
      ).unwrap()
    }
  }

  /** Returns the offset following this one. */
  pub fn nxt(& self) -> Self {
    Offset {
      offset: self.offset + 1u16
    }
  }

  /** Returns the offset preceeding this one if it's not 0. */
  pub fn pre(& self) -> Option<Self> {
    if self.offset == 0u16 { None } else {
      Some(
        Offset {
          offset: self.offset - 1u16
        }
      )
    }
  }
}

impl fmt::Display for Offset {
  fn fmt(& self, fmt: & mut fmt::Formatter) -> fmt::Result {
    write!(fmt, "{}", self.offset)
  }
}

impl Writable for Offset {
  fn write(& self, writer: & mut io::Write) -> io::Result<()> {
    write!(writer, "{}", self)
  }
}

/** Two-state offset. */
#[derive(Clone,Debug)]
pub struct Offset2 {
  /** Current offset. */
  curr: Offset,
  /** Next offset. */
  next: Offset,
}

impl Offset2 {
  /** Initial two-state offset. */
  pub fn init() -> Self {
    Offset2{
      curr: Offset::of_int(0),
      next: Offset::of_int(1),
    }
  }

  /** Reverses current and next. For backward unrolling. */
  pub fn rev(& self) -> Self {
    Offset2 { curr: self.next, next: self.curr }
  }

  /** Returns true iff the offset is reversed. */
  #[inline(always)]
  pub fn is_rev(& self) -> bool { self.next < self.curr }

  /** Compares two offsets. Used for parsing so that terms unrolled backwards
  are parsed the right way. For instance, `(and |@1 x| |@2 y|)` is parsed as
  `(and (next x) (curr y))` with Smt2Offset `Two(2,1)`. */
  #[inline]
  pub fn cmp(& self, lhs: & Offset, rhs: & Offset) -> ::std::cmp::Ordering {
    let cmp = lhs.cmp(rhs) ;
    if self.curr < self.next { cmp } else { cmp.reverse() }
  }

  /** Returns the two state offset following `self`. */
  #[inline(always)]
  pub fn nxt(& self) -> Self {
    Offset2 {
      curr: self.curr.nxt(),
      next: self.next.nxt(),
    }
  }

  /** The offset of the current state. */
  #[inline(always)]
  pub fn curr(& self) -> & Offset {
    & self.curr
  }

  /** The offset of the next state. */
  #[inline(always)]
  pub fn next(& self) -> & Offset {
    & self.next
  }
}

impl fmt::Display for Offset2 {
  fn fmt(& self, fmt: & mut fmt::Formatter) -> fmt::Result {
    write!(fmt, "({},{})", self.curr(), self.next())
  }
}


impl<Sym: SymWritable> SVarWriter<Sym> for Offset2 {
  fn sv_write(
    & self, writer: & mut io::Write,
    v: & Sym, st: & State, style: SymPrintStyle
  ) -> io::Result<()> {
    try!( write!(writer, "|@") ) ;
    match * st {
      State::Curr => try!( self.curr.write(writer) ),
      State::Next => try!( self.next.write(writer) ),
    } ;
    try!( v.write(writer, style) ) ;
    write!(writer, "|")
  }
}

impl<Sym: SymWritable> SVarWriter<Sym> for Offset {
  fn sv_write(
    & self, writer: & mut io::Write,
    v: & Sym, st: & State, style: SymPrintStyle
  ) -> io::Result<()> {
    try!( write!(writer, "|@") ) ;
    match * st {
      State::Curr => try!( self.write(writer) ),
      State::Next => panic!( "SVarWriter on Offset called on next svar" ),
    } ;
    try!( v.write(writer, style) ) ;
    write!(writer, "|")
  }
}

impl<Sym: SymWritable> SVarWriter<Sym> for () {
  fn sv_write(
    & self, writer: & mut io::Write,
    v: & Sym, st: & State, style: SymPrintStyle
  ) -> io::Result<()> {
    match * st {
      State::Curr => try!( write!(writer, "(state |") ),
      State::Next => try!( write!(writer, "(next |") ),
    } ;
    try!( v.write(writer, style) ) ;
    write!(writer, "|)")
  }
}



/** Indicates the offset of a term when parsing SMT Lib 2 expressions. */
#[derive(Debug,Clone,PartialEq,Eq)]
pub enum Smt2Offset {
  /** Term has no offset. */
  No,
  /** Term has only one offset: all state variables are current. */
  One(Offset),
  /** Term has two offsets: state variables are current and next. */
  Two(Offset, Offset),
}
impl fmt::Display for Smt2Offset {
  fn fmt(& self, fmt: & mut fmt::Formatter) -> fmt::Result {
    match * self {
      Smt2Offset::No => write!(fmt, "()"),
      Smt2Offset::One(o) => write!(fmt, "({})", o),
      Smt2Offset::Two(o1,o2) => write!(fmt, "({},{})", o1, o2),
    }
  }
}
impl Smt2Offset {
  /** Returns `No` offset if parameter is `None`, and `One` offset
  otherwise. */
  pub fn of_opt(opt: Option<Offset>) -> Self {
    use base::Smt2Offset::* ;
    match opt {
      None => No,
      Some(o) => One(o),
    }
  }

  /** Returns true iff `self` is `One(o)` and `rhs` is `Two(_, o)`. */
  pub fn is_next_of(& self, rhs: & Smt2Offset) -> bool {
    use base::Smt2Offset::* ;
    match (self, rhs) {
      (& One(ref lft), & Two(_, ref rgt)) => lft == rgt,
      _ => false
    }
  }

  /** Merges two offsets if possible.

  Two offsets are mergeable if

  * one is `No`,
  * both are equal,
  * both are `One`s (they will be ordered using `off.cmp(_,_)`),
  * one is `Two(lo,hi)` and the other is either `One(lo)` or `One(hi)`. */
  pub fn merge(
    & self, rhs: & Smt2Offset, off: & Offset2
  ) -> Option<Smt2Offset> {
    use std::cmp::{ Ordering, Ord } ;
    use base::Smt2Offset::* ;
    if self == rhs {
      Some( rhs.clone() )
    } else {
      let res = match (self,rhs) {
        (& No, _) => rhs.clone(),
        (_, & No) => self.clone(),

        (& One(ref lft), & One(ref rgt)) => match off.cmp(lft, rgt) {
          Ordering::Less => Smt2Offset::Two(*lft,*rgt),
          Ordering::Equal => rhs.clone(),
          Ordering::Greater => Smt2Offset::Two(*rgt,*lft),
        },

        (& Two(ref lft_lo, ref lft_hi), & One(ref rgt)) => {
          if rgt != lft_lo && rgt != lft_hi { return None } else {
            self.clone()
          }
        },

        /* This is only fine if both are equal which is handled above. */
        (& Two(_, _), & Two(_, _)) => return None,

        /* Only one recursive call is possible. */
        (& One(_), & Two(_,_)) => return rhs.merge(self, off),
      } ;
      Some(res)
    }
  }
}


/** Redefinition of the thread-safe hash consign type. */
pub type HConsign<T> = Arc<Mutex<HashConsign<T>>> ;

/** Can create itself from nothing. */
pub trait Mkable {
  /** Creates a new `Self` from unit. */
  fn mk() -> Self ;
}

impl<T: Hash> Mkable for Arc<Mutex<HashConsign<T>>>{
  fn mk() -> Self {
    Arc::new(
      Mutex::new( HashConsign::empty() )
    )
  }
}