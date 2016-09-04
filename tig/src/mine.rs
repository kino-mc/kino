// Copyright 2015 Adrien Champion. See the COPYRIGHT file at the top-level
// directory of this distribution.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! Candidate term mining functions.

use term::{ Factory, Term, TermSet } ;
use system::Sys ;

/// Mines a system for boolean candidate terms.
pub fn bool(factory: & Factory, sys: & Sys) -> (Term, TermSet) {
  use term::{ CstMaker, VarMaker, State } ;

  let svars = sys.state().args() ;
  let mut boo_svars = Vec::with_capacity( svars.len() / 3 ) ;
  // let int_svars = Vec::with_capacity( svars.len() / 3 ) ;
  // let rat_svars = Vec::with_capacity( svars.len() / 3 ) ;

  let mut result = TermSet::with_capacity( svars.len() * 10 ) ;

  for & (ref sym, ref typ) in svars.iter() {
    use term::Type::* ;
    match * typ {
      Bool => boo_svars.push( sym.clone() ),
      _ => (),
      // Int  => int_svars.push( sym.clone() ),
      // Rat  => rat_svars.push( sym.clone() ),
    }
  }

  for svar in boo_svars.into_iter() {
    let svar = factory.svar(svar, State::Next) ;
    let term = factory.mk_var(svar) ;
    let was_there = result.insert( term.clone() ) ;
    debug_assert!( ! was_there ) ;
    let term = factory.not(term) ;
    let was_there = result.insert( term ) ;
    debug_assert!( ! was_there )
  }

  let rep = factory.cst(false) ;
  result.remove(& rep) ;
  result.insert( factory.cst(true) ) ;
  (rep, result)
}