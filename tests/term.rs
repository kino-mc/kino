// Copyright 2015 Adrien Champion. See the COPYRIGHT file at the top-level
// directory of this distribution.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

/*! Tests for the term crate. */

extern crate kino_api as lib ;

pub use lib::{
  Factory, Offset2, Cst, Term
} ;
pub use lib::real_term::Cst as RCst ;

/** Test for terms. */
mod term {
  pub use super::* ;

  /** Test for the evaluation of terms. */
  mod eval {
    use super::* ;

    fn int(factory: & Factory, bytes: & [u8]) -> Term {
      use lib::CstMaker ;
      factory.cst( int_cst(factory, bytes) )
    }

    fn int_cst(factory: & Factory, bytes: & [u8]) -> Cst {
      use lib::BigInt ;
      use lib::CstMaker ;
      factory.cst( BigInt::parse_bytes(bytes, 10u32).unwrap() )
    }


    #[test]
    fn and() {
      use lib::CstMaker ;
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
      match factory.eval(& term, & offset, & model) {
        Ok(cst) => assert_eq!(res, cst),
        Err(s) => panic!("{}", s),
      }
    }

    #[test]
    fn or() {
      use lib::CstMaker ;
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
      match factory.eval(& term, & offset, & model) {
        Ok(cst) => assert_eq!(res, cst),
        Err(s) => panic!("{}", s),
      }
    }

    #[test]
    fn xor() {
      use lib::CstMaker ;
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
      match factory.eval(& term, & offset, & model) {
        Ok(cst) => assert_eq!(res, cst),
        Err(s) => panic!("{}", s),
      }
    }

    #[test]
    fn eq() {
      use lib::CstMaker ;
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
      match factory.eval(& term, & offset, & model) {
        Ok(cst) => assert_eq!(res, cst),
        Err(s) => panic!("{}", s),
      }
    }

    #[test]
    fn ite() {
      use lib::CstMaker ;
      let factory = Factory::mk() ;
      let term = factory.ite(
        factory.cst(false),
        int(& factory, b"52"),
        int(& factory, b"42")
      ) ;
      let res = int_cst(& factory, b"42") ;
      let model = vec![] ;
      let offset = Offset2::init() ;
      match factory.eval(& term, & offset, & model) {
        Ok(cst) => assert_eq!(res, cst),
        Err(s) => panic!("{}", s),
      }
    }

    #[test]
    fn imp() {
      use lib::CstMaker ;
      let factory = Factory::mk() ;
      let term = factory.imp(
        factory.cst(false),
        factory.cst(true),
      ) ;
      let res: Cst = factory.cst(true) ;
      let model = vec![] ;
      let offset = Offset2::init() ;
      match factory.eval(& term, & offset, & model) {
        Ok(cst) => assert_eq!(res, cst),
        Err(s) => panic!("{}", s),
      }
    }

    #[test]
    fn not() {
      use lib::CstMaker ;
      let factory = Factory::mk() ;
      let term = factory.not( factory.cst(true) ) ;
      let res: Cst = factory.cst(false) ;
      let model = vec![] ;
      let offset = Offset2::init() ;
      match factory.eval(& term, & offset, & model) {
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
      match factory.eval(& term, & offset, & model) {
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
      match factory.eval(& term, & offset, & model) {
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
      match factory.eval(& term, & offset, & model) {
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
      match factory.eval(& term, & offset, & model) {
        Ok(cst) => assert_eq!(res, cst),
        Err(s) => panic!("{}", s),
      }
    }

    #[test]
    fn le() {
      use lib::CstMaker ;
      let factory = Factory::mk() ;
      let term = factory.le(
        int(& factory, b"7"), int(& factory, b"35")
      ) ;
      let res: Cst = factory.cst(true) ;
      let model = vec![] ;
      let offset = Offset2::init() ;
      match factory.eval(& term, & offset, & model) {
        Ok(cst) => assert_eq!(res, cst),
        Err(s) => panic!("{}", s),
      }
    }

    #[test]
    fn lt() {
      use lib::CstMaker ;
      let factory = Factory::mk() ;
      let term = factory.lt(
        int(& factory, b"7"), int(& factory, b"35")
      ) ;
      let res: Cst = factory.cst(true) ;
      let model = vec![] ;
      let offset = Offset2::init() ;
      match factory.eval(& term, & offset, & model) {
        Ok(cst) => assert_eq!(res, cst),
        Err(s) => panic!("{}", s),
      }
    }

    #[test]
    fn ge() {
      use lib::CstMaker ;
      let factory = Factory::mk() ;
      let term = factory.ge(
        int(& factory, b"7"), int(& factory, b"35")
      ) ;
      let res: Cst = factory.cst(false) ;
      let model = vec![] ;
      let offset = Offset2::init() ;
      match factory.eval(& term, & offset, & model) {
        Ok(cst) => assert_eq!(res, cst),
        Err(s) => panic!("{}", s),
      }
    }

    #[test]
    fn gt() {
      use lib::CstMaker ;
      let factory = Factory::mk() ;
      let term = factory.gt(
        int(& factory, b"7"), int(& factory, b"35")
      ) ;
      let res: Cst = factory.cst(false) ;
      let model = vec![] ;
      let offset = Offset2::init() ;
      match factory.eval(& term, & offset, & model) {
        Ok(cst) => assert_eq!(res, cst),
        Err(s) => panic!("{}", s),
      }
    }
  }

}