// Copyright 2015 Adrien Champion. See the COPYRIGHT file at the top-level
// directory of this distribution.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

#![deny(missing_docs)]
#![allow(dead_code)]

//! Tinelli-style invariant generation.

extern crate term ;
extern crate system ;
extern crate common ;
extern crate unroll ;

use std::fmt ;
use std::cmp::Ord ;
use std::hash::{ Hash, Hasher } ;
use std::collections::{ HashSet, HashMap } ;
use std::marker::PhantomData ;

use term::{
  Offset2, Term, Operator,
  Factory,
  Bool, Int, Rat,
  Model
} ;


/// Key representing a node, corresponds to the key of its representant.
type Key = u64 ;

/// The value trait provides the operator encoding the ordering.
trait Val: Sized + Ord + Eq + Hash {
  /// The operator encording the ordering, e.g. `=>` for `Bool`.
  fn order_op() -> Operator ;
  /// Evaluates a term to some value given a model.
  fn eval(
    & Term, & Offset2, & Model, & Factory
  ) -> Result<Self, String> ;
}

impl Val for Bool {
  fn order_op() -> Operator { Operator::Impl }
  fn eval(
    term: & Term, offset: & Offset2, model: & Model, factory: & Factory
  ) -> Result<Bool, String> {
    factory.eval_bool(term, offset, model)
  }
}
impl Val for Int {
  fn order_op() -> Operator { Operator::Le }
  fn eval(
    term: & Term, offset: & Offset2, model: & Model, factory: & Factory
  ) -> Result<Int, String> {
    factory.eval_int(term, offset, model)
  }
}
impl Val for Rat {
  fn order_op() -> Operator { Operator::Le }
  fn eval(
    term: & Term, offset: & Offset2, model: & Model, factory: & Factory
  ) -> Result<Rat, String> {
    factory.eval_rat(term, offset, model)
  }
}

/// A node in the invariant generation graph.
struct Node<V> {
  /// Phantom data for the type the terms evaluate to.
  phantom: PhantomData<V>,
  /// Term representing the class.
  rep: Term,
  /// All terms of the node except `rep`.
  others: HashSet<Term>,
  /// The keys of the nodes directly above this one.
  above: HashSet<Key>,
  /// Stores the nodes potentially above this one after the split.
  above_transient: HashSet<Key>,
  /// The keys of the nodes directly below this one.
  below: HashSet<Key>,
}
impl<V: Val> Node<V> {
  /// Creates a new node.
  #[inline(always)]
  pub fn mk(rep: Term, others: HashSet<Term>) -> Self {
    debug_assert!(
      ! others.contains(& rep)
    ) ;
    Node {
      phantom: PhantomData,
      rep: rep,
      others: others,
      above: HashSet::new(),
      above_transient: HashSet::new(),
      below: HashSet::new(),
    }
  }
  /// Creates a new node with a representant and no other terms.
  #[inline(always)]
  pub fn of_rep(rep: Term) -> Self {
    Self::mk( rep, HashSet::new() )
  }

  /// The key of the node (hkey of the representant).
  #[inline(always)]
  pub fn key(& self) -> Key { self.rep.hkey() }

  /// Adds a term to the node.
  #[inline(always)]
  pub fn insert(& mut self, term: Term) -> bool {
    self.others.insert(term)
  }

  /// The nodes above this one.
  #[inline(always)]
  pub fn above(& self) -> & HashSet<Key> { & self.above }
  /// The nodes below this one.
  #[inline(always)]
  pub fn below(& self) -> & HashSet<Key> { & self.below }

  /// Adds a node above a node.
  #[inline(always)]
  pub fn add_above(& mut self, node: Key) -> bool {
    self.above.insert(node)
  }
  /// Adds a node below a node.
  #[inline(always)]
  pub fn add_below(& mut self, node: Key) -> bool {
    self.below.insert(node)
  }

  /// Removes a node above a node.
  #[inline(always)]
  pub fn rm_above(& mut self, node: Key) -> bool {
    self.above.remove(& node)
  }
  /// Removes a node below a node.
  #[inline(always)]
  pub fn rm_below(& mut self, node: Key) -> bool {
    self.below.remove(& node)
  }

  /** Returns the set of nodes below a node. Destroys the set `below` of the
  structure. */
  pub fn drain_below(& mut self) -> HashSet<Key> {
    let mut below = HashSet::new() ;
    ::std::mem::swap(& mut below, & mut self.below) ;
    below
  }

  /** Splits a node based on a model `mdl`.

  Returns the nodes `N_1`, ..., `N_n` such that

  * all elements of `N_i` are equal to some value `v_i` under `mdl`,
  * for `0 <= i < n`, `v_i \le v_{i+1}` where `\le` is the ordering on the
    values.

  Uses `insert_in_vec`. */
  pub fn split(
    self, model: & Model, offset: & Offset2, factory: & Factory
  ) -> Result<Vec<(V,Self)>, String> {
    debug_assert!( self.above.is_empty() ) ;
    debug_assert!( self.below.is_empty() ) ;
    let mut vec = vec![] ;
    match V::eval(& self.rep, offset, model, factory) {
      Ok(v) => vec.push( (v, Self::of_rep(self.rep)) ),
      Err(s) => return Err(s),
    } ;
    for term in self.others.into_iter() {
      match V::eval(& term, offset, model, factory) {
        Ok(v) => vec = insert_in_vec(vec, v, term),
        Err(s) => return Err(s),
      }
    } ;
    Ok(vec)
  }
}

/** Helper function for `split`, inserts a value / term pair in a sorted
value / node pair.

Inserts the term in the node corresponding to the value if any, otherwise
creates a new node with this term as representative. */
fn insert_in_vec<V: Val>(
  vec: Vec<(V, Node<V>)>, val: V, term: Term
) -> Vec<(V, Node<V>)> {
  use std::cmp::Ordering::* ;
  use std::iter::Extend ;
  let mut new = Vec::with_capacity(vec.len() + 1) ;
  let mut old = vec.into_iter() ;
  loop {
    if let Some( (v, mut node) ) = old.next() {
      match v.cmp(& val) {
        Less => new.push( (v, node) ),
        Equal => {
          node.insert(term) ;
          new.push( (v, node) ) ;
          break
        },
        Greater => {
          new.push( (v, node) ) ;
          new.push( (val, Node::of_rep(term)) ) ;
          break
        },
      }
    } else {
      new.push( (val, Node::of_rep(term)) ) ;
      break
    }
  }
  new.extend(old) ;
  new
}

impl<V> Hash for Node<V> {
  fn hash<H: Hasher>(& self, state: & mut H) {
    state.write_u64(self.rep.hkey())
  }
}

impl<V> fmt::Display for Node<V> {
  fn fmt(& self, fmt: & mut fmt::Formatter) -> fmt::Result {
    write!(
      fmt, "{}[{}]({}<{}<{})",
      self.rep.hkey(), self.rep.get(),
      self.above.len(), self.others.len(), self.below.len()
    )
  }
}



/// A graph is some roots and some nodes.
struct Graph<V> {
  /// Roots of the graph.
  roots: HashSet<Key>,
  /// Nodes of the graph.
  nodes: HashMap<Key, Node<V>>,
}
impl<V: Val> Graph<V> {
  /// The node and value associated with a key.
  #[inline(always)]
  pub fn node(& self, index: & Key) -> Option<& Node<V>> {
    self.nodes.get(index)
  }
  /// The node and value associated with a key (mutable).
  #[inline(always)]
  pub fn node_mut(
    & mut self, index: & Key
  ) -> Option<& mut Node<V>> {
    self.nodes.get_mut(index)
  }

  /** Extracts a root. Removes it from the set of nodes and returns the root
  and its kids. */
  #[inline]
  pub fn root(& mut self) -> Option<Node<V>> {
    let root = match self.roots.iter().next() {
      Some(key) => * key,
      None => return None,
    } ;
    let was_there = self.roots.remove(& root) ;
    debug_assert!( was_there ) ;
    match self.nodes.remove(& root) {
      Some( root ) => Some(root),
      None => panic!(
        "node {} is registered as root but unknown to set of nodes",
        root
      )
    }
  }

  /// Splits a graph according to a model.
  pub fn split(
    mut self, model: & Model, offset: & Offset2, factory: & Factory
  ) -> Result<Self, String> {
    // Orphan kids, kids we can process.
    let mut orphans = Vec::with_capacity(13) ;
    // The new graph we're building.
    let mut new = Graph {
      roots: HashSet::with_capacity(self.roots.len()),
      nodes: HashMap::with_capacity(self.nodes.len()),
    } ;

    // Handle all roots first.
    'roots: loop {
      if let Some(root) = self.root() {
        let old_key = root.key() ;

        // Splitting root.
        let mut ordered = match root.split(model, offset, factory) {
          Ok(ordered) => ordered, Err(s) => return Err(s)
        } ;

        // Adding biggest node, i.e. the new root.
        let mut prev = if let Some((_, root)) = ordered.pop() {
          let key = root.key() ;
          new.roots.insert(key) ;
          new.nodes.insert(key, root) ;
          key
        } else {
          return Err(
            format!("split of root {} resulted in nothing", old_key)
          )
        } ;

        // Looping over what's below the new root.
        'nu_kids: loop {
          if let Some((_, mut kid)) = ordered.pop() {
            kid.above.insert(prev) ;
            match new.nodes.get_mut(& prev) {
              Some(prev) => prev.below.insert(kid.key()),
              None => return Err(
                format!("unknown previous node {}", prev)
              ),
            } ;
            prev = kid.key() ;
            let was_there = new.nodes.insert(kid.key(), kid) ;
            debug_assert!(was_there.is_none())
          } else {
            break 'nu_kids
          }
        } ;

        // Removing the root from its kids, adding smallet new node as
        // transient. Remembering orphan kids.
        for kid in new.nodes.get_mut(& old_key).unwrap().above().iter() {
          match self.nodes.get_mut(kid) {
            Some(kid) => {
              let was_there = kid.rm_above(old_key) ;
              debug_assert!(was_there) ;
              let was_there = kid.above_transient.insert(prev) ;
              debug_assert!(! was_there) ;
              if kid.above.is_empty() {
                orphans.push(kid.key()) // Orphan, remember it.
              }
            },
            None => return Err(
              format!("unknown root with key {}", kid)
            ),
          }
        } ;
        ()
      } else { break 'roots }
    } ;

    // 'non_roots: loop {
    //   if let Some(node) = orphans.pop() {
    //     let old_key = node.key() ;

    //     // Split node.
    //     let mut ordered = match node.split(model, offset, factory) {
    //       Ok(ordered) => ordered,
    //       Err(s) => return Err(s),
    //     } ;

    //     // Updating biggest node.
    //     let mut prev = if let Some((_, node)) = ordered.pop() {
    //       let key = node.key() ;
    //       new.nodes.insert
    //     }


    //   } else { break 'non_roots }
    // } ;

    Ok(new)
  }
}

