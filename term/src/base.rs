// Copyright 2015 Adrien Champion. See the COPYRIGHT file at the top-level
// directory of this distribution.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

/*! Basic traits and structures. */

pub use hcons::* ;

use std::sync::{ Arc, Mutex } ;

/** Under the hood an offset is a `u16`. */
#[derive(Debug,PartialEq,Eq,PartialOrd,Ord,Hash,Clone,Copy)]
pub struct Offset(u16) ;

impl Offset {
  /** Bytes to Offset conversion. */
  pub fn of_bytes(bytes: & [u8]) -> Offset {
    // -> Result<Offset, std::num::ParseIntError> {
    use std::str ;
    Offset(
      u16::from_str_radix( str::from_utf8(bytes).unwrap(), 10 ).unwrap()
    )
  }
  /** `usize` to Offset conversion. */
  pub fn of_int(int: usize) -> Offset {
    Offset(
      u16::from_str_radix( & int.to_string(), 10 ).unwrap()
    )
  }
}

/** One-state offset. */
pub struct Offset1(Offset) ;

/** Two-state offset.

First is current step, second is next. */
pub struct Offset2(Offset, Offset) ;



/** Redefinition of the thread-safe hash consign type. */
pub type HConsign<T> = Arc<Mutex<HashConsign<T>>> ;


// pub mod cst {
//   use super::* ;
//   use super::typ::* ;
//   use self::Constant::* ;

//   #[derive(PartialEq,Eq,PartialOrd,Ord,Hash)]
//   pub enum Constant {
//     B(Bool),
//     I(Int),
//     R(Rat),
//   }

//   pub type Const = HConsed<Constant> ;

//   pub type ConstConsign = HConsign<Constant> ;

//   pub trait ConstFactory {
//     fn of_bool(& self, b: Bool) -> Const ;
//     fn of_int(& self, b: Int) -> Const ;
//     fn of_rat(& self, b: Rat) -> Const ;
//   }

//   impl ConstFactory for ConstConsign {
//     fn of_bool(& self, b: Bool) -> Const {
//       self.lock().unwrap().mk( B(b) )
//     }
//     fn of_int(& self, i: Int) -> Const {
//       self.lock().unwrap().mk( I(i) )
//     }
//     fn of_rat(& self, r: Rat) -> Const {
//       self.lock().unwrap().mk( R(r) )
//     }
//   }
// }

// pub mod var {
//   use super::* ;
//   use self::Variable::* ;

//   #[derive(PartialEq,Eq,PartialOrd,Ord,Hash)]
//   pub enum Variable {
//     NSVar(id::Id),
//     SVar0(id::Id),
//     SVar1(id::Id),
//   }

//   pub type Var = HConsed<Variable> ;

//   pub type VarConsign = HConsign<Variable> ;

//   pub trait VarFactory {
//     fn nsvar(& self, id: id::Id) -> Var ;
//     fn svar0(& self, id: id::Id) -> Var ;
//     fn svar1(& self, id: id::Id) -> Var ;
//   }

//   impl VarFactory for VarConsign {
//     fn nsvar(& self, id: id::Id) -> Var {
//       self.lock().unwrap().mk( NSVar(id) )
//     }
//     fn svar0(& self, id: id::Id) -> Var {
//       self.lock().unwrap().mk( SVar0(id) )
//     }
//     fn svar1(& self, id: id::Id) -> Var {
//       self.lock().unwrap().mk( SVar1(id) )
//     }
//   }
// }