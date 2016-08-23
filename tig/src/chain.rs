// Copyright 2015 Adrien Champion. See the COPYRIGHT file at the top-level
// directory of this distribution.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use term::{ Term, TermSet } ;

use Domain ;

/** A chain is an increasing-ordered list containing values and
representative / equivalence class pairs.

It is ordered on the values. */
#[derive(PartialEq, Eq, Clone)]
pub enum Chain< Val: Domain, Info: PartialEq + Eq + Clone > {
  /** Empty chain. */
  Nil,
  /** Chain constructor. */
  Cons(Val, Term, Info, Box< Chain<Val, Info> >),
}
impl<Val: Domain, Info: PartialEq + Eq + Clone> Chain<Val, Info> {
  /** Empty chain. */
  #[inline]
  pub fn nil() -> Self { Chain::Nil }
  /** Chain constructor. */
  #[inline]
  pub fn cons(self, v: Val, t: Term, s: Info) -> Self {
    Chain::Cons(v, t, s, Box::new(self))
  }
  /** Checks if a chain is empty. */
  #[inline]
  pub fn is_empty(& self) -> bool { * self == Chain::Nil }
  /** Returns the top value of a chain, if any. */
  #[inline]
  pub fn top_value(& self) -> Option<(Val, Term)> {
    use self::Chain::* ;
    match * self {
      Cons(ref v, ref rep, _, _) => Some( (v.clone(), rep.clone()) ),
      Nil => None,
    }
  }

  /** Returns the longest subchain of a chain the values of which are
  all greater than or equal to some value, and the rest of the chain.

  First subchain is a vector of representatives and is sorted in **increasing
  order** on their value (which have been removed at this point).
  The second subchain is an actual `Chain` and is still sorted in **decreasing
  order**. */
  pub fn split_at(mut self, value: & Val) -> (Vec<Term>, Self) {
    use self::Chain::* ;
    let mut res = Vec::with_capacity(3) ;
    loop {
      if let Cons(val, rep, set, tail) = self {
        if value <= & val {
          res.push(rep) ;
          self = * tail
        } else {
          // We have `val < value`, stop here.
          self = Cons(val, rep, set, tail) ;
          break
        }
      } else {
        // Chain is empty, we done.
        break
      }
    }
    (res, self)
  }

  /** Reverses the first chain and appends it to the second one. */
  #[inline]
  pub fn rev_append(mut self, mut that: Self) -> Self {
    use self::Chain::* ;
    while let Cons(val, term, set, tail) = self {
      that = Cons( val, term, set, Box::new(that) ) ;
      self = * tail
    }
    that
  }
  /** Reverses a chain. */
  #[inline]
  pub fn rev(self) -> Self {
    self.rev_append(Chain::Nil)
  }
}
impl<Val: Domain> Chain<Val, TermSet> {
  /** Maps to `Chain<Val, ()>`, calling a function on each element. */
  pub fn map_to_unit<
    Input, F: Fn(& mut Input, Val, Term, TermSet)
  >(mut self, f: F, i: & mut Input) -> Chain<Val, ()> {
    use self::Chain::* ;
    let mut res = Nil ;
    while let Cons(val, rep, set, tail) = self {
      self = * tail ;
      f(i, val.clone(), rep.clone(), set) ;
      res = res.cons(val, rep, ())
    }
    res.rev()
  }

  /** Inserts a term in a chain given its value. */
  pub fn insert(mut self, v: Val, t: Term) -> Result<Self, String> {
    use self::Chain::* ;
    use std::cmp::Ordering::* ;
    let mut prefix = Nil ;
    loop {
      if let Cons(val, term, mut set, tail) = self {
        match val.cmp(& v) {
          Less => return Ok(
            // Insert term found as a new node in the chain.
            prefix.rev_append(
              Cons(val, term, set, tail).cons(v, t, TermSet::new())
            )
          ),
          Equal => {
            // Insert term in the set of this node.
            debug_assert!( ! set.contains(& t) ) ;
            let _ = set.insert(t) ;
            return Ok( prefix.rev_append( Cons(val, term, set, tail) ) )
          },
          Greater => {
            // Need to go deeper, iterating.
            prefix = prefix.cons(val, term, set) ;
            self = * tail
          },
        }
      } else {
        // Reached end of list, inserting.
        return Ok(
          prefix.rev_append( Nil.cons(v, t, TermSet::new()) )
        )
      }
    }
  }
}