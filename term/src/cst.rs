// Copyright 2015 Adrien Champion. See the COPYRIGHT file at the top-level
// directory of this distribution.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! Constants.

use std::io ;
use std::fmt ;

use base::{ Writable, HConsed, HConsign, HConser } ;
use typ ;

use self::RealCst::* ;

/// Underlying representation of constants.
#[derive(
  Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash
)]
pub enum RealCst {
  /// Boolean constant.
  Bool(typ::Bool),
  /// Integer constant.
  Int(typ::Int),
  /// Rational constant.
  Rat(typ::Rat),
}

impl RealCst {
  /// The type of a `RealCst`.
  pub fn typ(& self) -> typ::Type {
    match * self {
      Bool(_) => typ::Type::Bool,
      Int(_) => typ::Type::Int,
      Rat(_) => typ::Type::Rat,
    }
  }

  /// Adds two constants if possible.
  pub fn add(& self, rhs: & Self) -> Result<Self, Self> {
    match * self {
      Bool(_) => Err(self.clone()),
      Int(ref lhs) => match * rhs {
        Int(ref rhs) => Ok( Int(lhs + rhs) ),
        _ => Err(rhs.clone()),
      },
      Rat(ref lhs) => match * rhs {
        Rat(ref rhs) => Ok( Rat(lhs + rhs) ),
        _ => Err(rhs.clone()),
      },
    }
  }

  /// Substracts two constants if possible.
  pub fn sub(& self, rhs: & Self) -> Result<Self, Self> {
    match * self {
      Bool(_) => Err(self.clone()),
      Int(ref lhs) => match * rhs {
        Int(ref rhs) => Ok( Int(lhs - rhs) ),
        _ => Err(rhs.clone()),
      },
      Rat(ref lhs) => match * rhs {
        Rat(ref rhs) => Ok( Rat(lhs - rhs) ),
        _ => Err(rhs.clone()),
      },
    }
  }

  /// Multiplies two constants if possible.
  pub fn mul(& self, rhs: & Self) -> Result<Self, Self> {
    match * self {
      Bool(_) => Err(self.clone()),
      Int(ref lhs) => match * rhs {
        Int(ref rhs) => Ok( Int(lhs * rhs) ),
        _ => Err(rhs.clone()),
      },
      Rat(ref lhs) => match * rhs {
        Rat(ref rhs) => Ok( Rat(lhs * rhs) ),
        _ => Err(rhs.clone()),
      },
    }
  }

  /// Divides two constants if possible.
  pub fn div(& self, in_rhs: & Self) -> Result<Self, Self> {
    use num::traits::Zero ;
    match * self {
      Int(ref lhs) => match * in_rhs {
        Int(ref rhs) => if rhs.is_zero() {
          Err(in_rhs.clone())
        } else {
          Ok( Int(lhs / rhs) )
        },
        _ => Err(in_rhs.clone()),
      },
      Rat(ref lhs) => match * in_rhs {
        Rat(ref rhs) => if rhs.is_zero() {
          Err(in_rhs.clone())
        } else {
          Ok( Rat(lhs / rhs) )
        },
        _ => Err(in_rhs.clone()),
      },
      _ => Err(self.clone()),
    }
  }

  /// Negates a constant if possible.
  pub fn neg(& self) -> Result<Self, Self> {
    match * self {
      Bool(_) => Err(self.clone()),
      Int(ref v) => Ok( Int(- v) ),
      Rat(ref v) => Ok( Rat(- v) ),
    }
  }
}

impl fmt::Display for RealCst {
  fn fmt(& self, fmt: & mut fmt::Formatter) -> fmt::Result {
    match * self {
      Bool(ref b) => write!(fmt, "{}", b),
      Int(ref i) => write!(fmt, "{}", i),
      Rat(ref r) => write!(fmt, "{}", r),
    }
  }
}

/// Hash consed constant.
pub type Cst = HConsed<RealCst> ;

impl Writable for Cst {
  #[inline(always)]
  fn write(& self, writer: & mut io::Write) -> io::Result<()> {
    match * self.get() {
      Bool(ref b) => write!( writer, "{}", b ),
      Int(ref i) => write!( writer, "{}", i ),
      Rat(ref r) => write!( writer, "(/ {} {})", r.numer(), r.denom() ),
    }
  }
}

/// Hash cons table for constants.
pub type CstConsign = HConsign<RealCst> ;

/// Can create a hash consed constant.
pub trait ConstMaker<Const> {
  /// Creates a hash consed constant.
  #[inline(always)]
  fn constant(& self, Const) -> Cst ;
}

impl<
  'a, Const: Clone, T: Sized + ConstMaker<Const>
> ConstMaker<& 'a Const> for T {
  fn constant(& self, cst: & 'a Const) -> Cst {
    (self as & ConstMaker<Const>).constant(cst.clone())
  }
}
impl ConstMaker<typ::Bool> for CstConsign {
  fn constant(& self, b: typ::Bool) -> Cst {
    self.mk( Bool(b) )
  }
}
impl ConstMaker<typ::Int> for CstConsign {
  fn constant(& self, i: typ::Int) -> Cst {
    self.mk( Int(i) )
  }
}
impl ConstMaker<typ::Rat> for CstConsign {
  fn constant(& self, r: typ::Rat) -> Cst {
    self.mk( Rat(r) )
  }
}
impl ConstMaker<RealCst> for CstConsign {
  fn constant(& self, cst: RealCst) -> Cst {
    self.mk( cst )
  }
}
