// Copyright 2015 Adrien Champion. See the COPYRIGHT file at the top-level
// directory of this distribution.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! Tests for the evaluator.

extern crate term ;

use term::{
  BigInt, Factory, Cst, Term, CstMaker, SymMaker, Offset2
} ;

/// Creates a constant integer term.
pub fn int(factory: & Factory, bytes: & [u8]) -> Term {
  factory.cst( int_cst(factory, bytes) )
}

/// Createts a constant integer `Cst`.
pub fn int_cst(factory: & Factory, bytes: & [u8]) -> Cst {
  factory.cst( BigInt::parse_bytes(bytes, 10u32).unwrap() )
}


#[test]
fn and() {
  let factory = Factory::mk() ;
  let kids = vec![
    factory.cst(true),
    factory.cst(true),
    factory.cst(false),
    factory.cst(true),
  ] ;
  let term = factory.and(kids) ;
  let res: Cst = factory.cst(false) ;
  let model = vec![] ;
  let offset = Offset2::init() ;
  let scope = factory.sym("whatever") ;
  match factory.eval(& term, & offset, & model, scope) {
    Ok(cst) => assert_eq!(res, cst),
    Err(s) => panic!("{}", s),
  }
}

#[test]
fn or() {
  let factory = Factory::mk() ;
  let kids = vec![
    factory.cst(true),
    factory.cst(true),
    factory.cst(false),
    factory.cst(true),
  ] ;
  let term = factory.or(kids) ;
  let res: Cst = factory.cst(true) ;
  let model = vec![] ;
  let offset = Offset2::init() ;
  let scope = factory.sym("whatever") ;
  match factory.eval(& term, & offset, & model, scope) {
    Ok(cst) => assert_eq!(res, cst),
    Err(s) => panic!("{}", s),
  }
}

#[test]
fn xor() {
  let factory = Factory::mk() ;
  let kids = vec![
    factory.cst(true),
    factory.cst(true),
    factory.cst(false),
    factory.cst(true),
  ] ;
  let term = factory.xor(kids) ;
  let res: Cst = factory.cst(false) ;
  let model = vec![] ;
  let offset = Offset2::init() ;
  let scope = factory.sym("whatever") ;
  match factory.eval(& term, & offset, & model, scope) {
    Ok(cst) => assert_eq!(res, cst),
    Err(s) => panic!("{}", s),
  }
}

#[test]
fn eq() {
  let factory = Factory::mk() ;
  let kids = vec![
    int(& factory, b"52"),
    int(& factory, b"52"),
    int(& factory, b"52")
  ] ;
  let term = factory.eq(kids) ;
  let res: Cst = factory.cst(true) ;
  let model = vec![] ;
  let offset = Offset2::init() ;
  let scope = factory.sym("whatever") ;
  match factory.eval(& term, & offset, & model, scope) {
    Ok(cst) => assert_eq!(res, cst),
    Err(s) => panic!("{}", s),
  }
}

#[test]
fn ite() {
  let factory = Factory::mk() ;
  let term = factory.ite(
    factory.cst(false),
    int(& factory, b"52"),
    int(& factory, b"42")
  ) ;
  let res = int_cst(& factory, b"42") ;
  let model = vec![] ;
  let offset = Offset2::init() ;
  let scope = factory.sym("whatever") ;
  match factory.eval(& term, & offset, & model, scope) {
    Ok(cst) => assert_eq!(res, cst),
    Err(s) => panic!("{}", s),
  }
}

#[test]
fn imp() {
  let factory = Factory::mk() ;
  let term = factory.imp(
    factory.cst(false),
    factory.cst(true),
  ) ;
  let res: Cst = factory.cst(true) ;
  let model = vec![] ;
  let offset = Offset2::init() ;
  let scope = factory.sym("whatever") ;
  match factory.eval(& term, & offset, & model, scope) {
    Ok(cst) => assert_eq!(res, cst),
    Err(s) => panic!("{}", s),
  }
}

#[test]
fn not() {
  let factory = Factory::mk() ;
  let term = factory.not( factory.cst(true) ) ;
  let res: Cst = factory.cst(false) ;
  let model = vec![] ;
  let offset = Offset2::init() ;
  let scope = factory.sym("whatever") ;
  match factory.eval(& term, & offset, & model, scope) {
    Ok(cst) => assert_eq!(res, cst),
    Err(s) => panic!("{}", s),
  }
}




#[test]
fn add() {
  let factory = Factory::mk() ;
  let kids = vec![ int(& factory, b"7"), int(& factory, b"35") ] ;
  let term = factory.add(kids) ;
  let res = int_cst(& factory, b"42") ;
  let model = vec![] ;
  let offset = Offset2::init() ;
  let scope = factory.sym("whatever") ;
  match factory.eval(& term, & offset, & model, scope) {
    Ok(cst) => assert_eq!(res, cst),
    Err(s) => panic!("{}", s),
  }
}

#[test]
fn sub() {
  let factory = Factory::mk() ;
  let kids = vec![ int(& factory, b"7"), int(& factory, b"35") ] ;
  let term = factory.sub(kids) ;
  let res = int_cst(& factory, b"-28") ;
  let model = vec![] ;
  let offset = Offset2::init() ;
  let scope = factory.sym("whatever") ;
  match factory.eval(& term, & offset, & model, scope) {
    Ok(cst) => assert_eq!(res, cst),
    Err(s) => panic!("{}", s),
  }
}

#[test]
fn mul() {
  let factory = Factory::mk() ;
  let kids = vec![ int(& factory, b"7"), int(& factory, b"35") ] ;
  let term = factory.mul(kids) ;
  let res = int_cst(& factory, b"245") ;
  let model = vec![] ;
  let offset = Offset2::init() ;
  let scope = factory.sym("whatever") ;
  match factory.eval(& term, & offset, & model, scope) {
    Ok(cst) => assert_eq!(res, cst),
    Err(s) => panic!("{}", s),
  }
}

#[test]
fn div() {
  let factory = Factory::mk() ;
  let term = factory.div(
    int(& factory, b"7"), int(& factory, b"35")
  ) ;
  let res = int_cst(& factory, b"0") ;
  let model = vec![] ;
  let offset = Offset2::init() ;
  let scope = factory.sym("whatever") ;
  match factory.eval(& term, & offset, & model, scope) {
    Ok(cst) => assert_eq!(res, cst),
    Err(s) => panic!("{}", s),
  }
}

#[test]
fn le() {
  let factory = Factory::mk() ;
  let term = factory.le(
    int(& factory, b"7"), int(& factory, b"35")
  ) ;
  let res: Cst = factory.cst(true) ;
  let model = vec![] ;
  let offset = Offset2::init() ;
  let scope = factory.sym("whatever") ;
  match factory.eval(& term, & offset, & model, scope) {
    Ok(cst) => assert_eq!(res, cst),
    Err(s) => panic!("{}", s),
  }
}

#[test]
fn lt() {
  let factory = Factory::mk() ;
  let term = factory.lt(
    int(& factory, b"7"), int(& factory, b"35")
  ) ;
  let res: Cst = factory.cst(true) ;
  let model = vec![] ;
  let offset = Offset2::init() ;
  let scope = factory.sym("whatever") ;
  match factory.eval(& term, & offset, & model, scope) {
    Ok(cst) => assert_eq!(res, cst),
    Err(s) => panic!("{}", s),
  }
}

#[test]
fn ge() {
  let factory = Factory::mk() ;
  let term = factory.ge(
    int(& factory, b"7"), int(& factory, b"35")
  ) ;
  let res: Cst = factory.cst(false) ;
  let model = vec![] ;
  let offset = Offset2::init() ;
  let scope = factory.sym("whatever") ;
  match factory.eval(& term, & offset, & model, scope) {
    Ok(cst) => assert_eq!(res, cst),
    Err(s) => panic!("{}", s),
  }
}

#[test]
fn gt() {
  let factory = Factory::mk() ;
  let term = factory.gt(
    int(& factory, b"7"), int(& factory, b"35")
  ) ;
  let res: Cst = factory.cst(false) ;
  let model = vec![] ;
  let offset = Offset2::init() ;
  let scope = factory.sym("whatever") ;
  match factory.eval(& term, & offset, & model, scope) {
    Ok(cst) => assert_eq!(res, cst),
    Err(s) => panic!("{}", s),
  }
}
