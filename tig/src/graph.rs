// Copyright 2015 Adrien Champion. See the COPYRIGHT file at the top-level
// directory of this distribution.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use std::fmt::Display ;
use std::io ;

use common::Res ;

use term::{
  Factory, Cst,
  Term, TermSet, TermMap,
  Bool, Int, Rat,
} ;

use eval::Eval ;

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

// /// Iterator over a chain.
// pub struct ChainIterator< 'a, Val: Domain + 'a, Info: PartialEq + Eq > {
//   chain: & 'a Chain<Val, Info>
// }
// impl<
//   'a, Val: Domain + 'a, Info: PartialEq + Eq
// > ::std::iter::Iterator for ChainIterator<'a, Val> {
//   type Item = (& 'a Val, & 'a Term, & 'a TermSet) ;
//   fn next(& mut self) -> Option<Self::Item> {
//     use self::Chain::* ;
//     match * self.chain {
//       Cons(ref v, ref t, ref s, ref tail) => {
//         self.chain = & (* * tail) ;
//         Some( (v, t, s) )
//       },
//       Nil => None,
//     }
//   }
// }


/** Trait for domains.

Domains define the type of the values the candidate terms evaluate to and a
total order relation used for the edges in the graph. */
pub trait Domain : PartialEq + Eq + PartialOrd + Ord + Clone + Display {
  /** A value from a constant. */
  fn of_cst(& Cst) -> Result<Self, String> ;
  /** Creates a term encoding a relation between terms. */
  fn mk_cmp(& mut Factory, Term, Term) -> Term ;
}
impl Domain for Bool {
  fn of_cst(cst: & Cst) -> Result<Self, String> {
    match * cst.get() {
      ::term::real_term::Cst::Bool(b) => Ok(b),
      ref cst => Err(
        format!("[Bool::of_cst] unexpected constant {}", cst)
      ),
    }
  }
  fn mk_cmp(f: & mut Factory, lhs: Term, rhs: Term) -> Term {
    f.imp(lhs, rhs)
  }
}
impl Domain for Int  {
  fn of_cst(cst: & Cst) -> Result<Self, String> {
    match * cst.get() {
      ::term::real_term::Cst::Int(ref i) => Ok(i.clone()),
      ref cst => Err(
        format!("[Int::of_cst] unexpected constant {}", cst)
      ),
    }
  }
  fn mk_cmp(f: & mut Factory, lhs: Term, rhs: Term) -> Term {
    f.le(lhs, rhs)
  }
}
impl Domain for Rat  {
  fn of_cst(cst: & Cst) -> Result<Self, String> {
    match * cst.get() {
      ::term::real_term::Cst::Rat(ref r) => Ok(r.clone()),
      ref cst => Err(
        format!("[Rat::of_cst] unexpected constant {}", cst)
      ),
    }
  }
  fn mk_cmp(f: & mut Factory, lhs: Term, rhs: Term) -> Term {
    f.le(lhs, rhs)
  }
}


/** The graph structure, storing the nodes and the edges. */
pub struct Graph<Val: Domain> {
  /** Forward edges between representatives. */
  map_for: TermMap<TermSet>,
  /** Backward edges between representatives. */
  map_bak: TermMap<TermSet>,
  /** Maps representatives to their class. */
  classes: TermMap<TermSet>,
  /** Remembers which classes have already been stabilized.
  Stores the representatives. */
  memory: TermSet,
  /** Stores the representatives that have been split and their value. */
  values: TermMap<Val>,
}

impl<Val: Domain> Graph<Val> {

  /** Creates an empty graph. */
  #[inline]
  fn with_capacity(capa: usize) -> Self {
    Graph {
      map_for: TermMap::with_capacity( capa ),
      map_bak: TermMap::with_capacity( capa ),
      classes: TermMap::with_capacity( capa ),
      memory:  TermSet::with_capacity( capa ),
      values:  TermMap::with_capacity( capa ),
    }
  }

  /** Creates a new graph from a unique equivalence class. */
  #[inline]
  pub fn mk(rep: Term, class: TermSet) -> Self {
    // Creating empty graph.
    let mut graph = Graph::with_capacity(class.len() / 3) ;
    // `rep` has no kids.
    graph.map_for.insert(
      rep.clone(), TermSet::with_capacity(class.len() / 10)
    ) ;
    // `rep` has no parents.
    graph.map_bak.insert(
      rep.clone(), TermSet::with_capacity(class.len() / 10)
    ) ;
    // `rep`'s class is the one provided.
    graph.classes.insert(rep, class) ;
    // Done.
    graph
  }

  /** Adds kids to a representative. Updates `map_for` and `map_bak`. */
  pub fn add_kids(
    & mut self, rep: & Term, kids: TermSet
  ) -> Result<(), String> {
    // Update backward edges.
    for kid in kids.iter() {
      match self.map_bak.get_mut(kid) {
        // Add parent to parents.
        Some(set) => {
          let _ = set.insert(rep.clone()) ;
          continue
        },
        // Add parent as new set.
        None => (),
      } ;
      let mut set = TermSet::new() ;
      set.insert(rep.clone()) ;
      let _ = self.map_bak.insert(kid.clone(), set) ;
      ()
    }

    // Update forward edges.
    match self.map_for.remove(rep) {
      Some(mut set) => {
        for kid in kids.into_iter() {
          set.insert(kid) ;
        }
        // Add the new kids.
        self.map_for.insert(rep.clone(), set) ;
      },
      None => return Err(
        format!("[add_kids] unknown rep {}", rep)
      ),
    }

    Ok(())
  }

  /** Adds kids to a representative. Updates `map_for` and `map_bak`.

  Version where `kids` is a reference. */
  pub fn add_kids_ref(
    & mut self, rep: & Term, kids: & TermSet
  ) -> Result<(), String> {
    // Update backward edges.
    for kid in kids.iter() {
      match self.map_bak.get_mut(kid) {
        // Add parent to parents.
        Some(set) => {
          let _ = set.insert(rep.clone()) ;
          continue
        },
        // Add parent as new set.
        None => (),
      } ;
      let mut set = TermSet::new() ;
      set.insert(rep.clone()) ;
      let _ = self.map_bak.insert(kid.clone(), set) ;
      ()
    }

    // Update forward edges.
    match self.map_for.remove(rep) {
      Some(mut set) => {
        for kid in kids.iter() {
          set.insert(kid.clone()) ;
        }
        // Add the new kids.
        self.map_for.insert(rep.clone(), set) ;
      },
      None => return Err(
        format!("[add_kids] unknown rep {}", rep)
      ),
    }

    Ok(())
  }

  /** Formats a graph in dot format. */
  pub fn dot_fmt<W: io::Write>(& self, w: & mut W) -> io::Result<()> {
    // Header.
    try!(
      write!(
        w,
        "\
digraph mode_graph {{
  graph [bgcolor=black margin=0.0] ;
  node [
    style=filled
    fillcolor=black
    fontcolor=\"#1e90ff\"
    color=\"#666666\"
  ] ;
  edge [color=\"#1e90ff\" fontcolor=\"#222222\"] ;

\
        "
      )
    ) ;

    // Printing edges forward.
    for (rep, kids) in self.map_for.iter() {
      let size = match self.classes.get(rep) {
        Some(class) => class.len(),
        None => panic!(
          "[dot_fmt] rep {} has no equivalence class", rep
        )
      } ;
      let value = match self.values.get(rep) {
        Some(v) => format!("{}", v),
        None => format!("_"),
      } ;
      for kid in kids.iter() {
        let kid_size = match self.classes.get(kid) {
          Some(class) => class.len(),
          None => panic!(
            "[dot_fmt] rep {} has no equivalence class", kid
          )
        } ;
        let kid_value = match self.values.get(kid) {
          Some(v) => format!("{}", v),
          None => format!("_"),
        } ;
        try!(
          write!(
            w,
            "  \
              \"{} ({}, {})\" -> \"{} ({}, {})\" [\n    \
                constraint = false\n  \
              ] ;\n\
            ", rep, size, value, kid, kid_size, kid_value
          )
        )
      }
    } ;

    // Printing edges backward.
    for (rep, parents) in self.map_bak.iter() {
      let size = match self.classes.get(rep) {
        Some(class) => class.len(),
        None => panic!(
          "[dot_fmt] rep {} has no equivalence class", rep
        )
      } ;
      let value = match self.values.get(rep) {
        Some(v) => format!("{}", v),
        None => format!("_"),
      } ;
      for parent in parents.iter() {
        let parent_size = match self.classes.get(parent) {
          Some(class) => class.len(),
          None => panic!(
            "[dot_fmt] rep {} has no equivalence class", parent
          )
        } ;
        let parent_value = match self.values.get(parent) {
          Some(v) => format!("{}", v),
          None => format!("_"),
        } ;
        try!(
          write!(
            w,
            "  \
              \"{} ({}, {})\" -> \"{} ({}, {})\" [\n    \
                color = \"red\"\n  \
              ] ;\n\
            ", parent, parent_size, parent_value, rep, size, value
          )
        )
      }
    } ;
    write!(w, "}}\n")
  }

  /** Class corresponding to a representative. */
  #[inline]
  pub fn class_of<'a, 'b>(
    & 'a self, rep: & 'b Term
  ) -> Result<& 'a TermSet, String> {
    match self.classes.get(rep) {
      Some(set) => Ok(set),
      None => Err(
        format!("[Graph::class_of] representative {} is unknown", rep)
      ),
    }
  }

  /** Class corresponding to a representative (mutable version). */
  #[inline]
  pub fn class_mut_of<'a, 'b>(
    & 'a mut self, rep: & 'b Term
  ) -> Result<& 'a mut TermSet, String> {
    match self.classes.get_mut(rep) {
      Some(set) => Ok(set),
      None => Err(
        format!("[Graph::class_mut_of] representative {} is unknown", rep)
      ),
    }
  }

  /** Kids corresponding of a representative. */
  #[inline]
  pub fn kids_of<'a, 'b>(
    & 'a self, rep: & 'b Term
  ) -> Result<& 'a TermSet, String> {
    match self.map_for.get(rep) {
      Some(set) => Ok(set),
      None => Err(
        format!("[Graph::kids_of] representative {} is unknown", rep)
      ),
    }
  }

  /** Kids corresponding to a representative (mutable version). */
  #[inline]
  pub fn kids_mut_of<'a, 'b>(
    & 'a mut self, rep: & 'b Term
  ) -> Result<& 'a mut TermSet, String> {
    match self.map_for.get_mut(rep) {
      Some(set) => Ok(set),
      None => Err(
        format!("[Graph::kids_mut_of] representative {} is unknown", rep)
      ),
    }
  }

  /** Parents corresponding of a representative. */
  #[inline]
  pub fn parents_of<'a, 'b>(
    & 'a self, rep: & 'b Term
  ) -> Result<& 'a TermSet, String> {
    match self.map_bak.get(rep) {
      Some(set) => Ok(set),
      None => Err(
        format!("[Graph::parents_of] representative {} is unknown", rep)
      ),
    }
  }

  /** Parents corresponding to a representative (mutable version). */
  #[inline]
  pub fn parents_mut_of<'a, 'b>(
    & 'a mut self, rep: & 'b Term
  ) -> Result<& 'a mut TermSet, String> {
    match self.map_bak.get_mut(rep) {
      Some(set) => Ok(set),
      None => Err(
        format!("[Graph::parents_mut_of] representative {} is unknown", rep)
      ),
    }
  }

  /** Clears the stabilization memory. Call before starting a stabilization
  step. */
  #[inline]
  pub fn clear_memory(& mut self) {
    self.memory.clear()
  }

  /** Removes a term from a class corresponding to a representative. */
  pub fn drop_member(
    & mut self, rep: & Term, elem: & Term
  ) -> Res<()> {
    // Getting the right equivalence class. */
    let class = try_str!(
      self.class_mut_of(rep),
      "[drop_member] retrieving class of {}", rep
    ) ;
    // Removing element.
    let was_there = class.remove(elem) ;
    if ! was_there {
      Err(
        vec![
          format!(
            "[drop_member] {} is not an element of the class of {}",
            elem, rep
          )
        ]
      )
    } else { Ok(()) }
  }

  /** Splits a class corresponding to a representative, given an evaluator.

  Returns a chain.

  Only modifies the `classes` and `values` fields of the graph to break
  `rep`'s class and create the ones encoded in the final chain, and update the
  values of the different representatives. */
  pub fn split_class(
    & mut self, rep: & Term, eval: & mut Eval<Val>
  ) -> Res< Chain<Val, ()> > {
    // Starting with an empty chain.
    let mut chain = Chain::nil() ;
    
    {
      let class = match self.classes.get(rep) {
        Some(class) => class,
        None => return Err(
          vec![
            format!("[split_class] representative {} is unknown", rep)
          ]
        ),
      } ;
      // Evaluate representative first.
      chain = try_str!(
        chain.insert(
          try_str!(
            eval.eval(rep), "[split_class] while evaluating representative"
          ),
          rep.clone()
        ),
        "[split_class] while inserting representative in the chain"
      ) ;
      // Evaluate everyone and insert as needed.
      for term in class.iter() {
        chain = try_str!(
          chain.insert(
            try_str!(
              eval.eval(term),
              "[split_class] while evaluating term for rep {}", rep
            ),
            term.clone()
          ),
          "[split_class] while inserting in chain for rep {}", rep
        ) ;
      }
    } ;

    // Update `classes` and `values`.
    let chain = chain.map_to_unit(
      |graph, v, rep, set| {
        let _ = graph.values.insert(rep.clone(), v) ;
        let _ = graph.classes.insert(rep, set) ;
        ()
      },
      self
    ) ;
    // Return the chain.
    Ok(chain)
  }

  /** Inserts a chain in a graph. */
  pub fn insert_chain(
    & mut self, rep: & Term, chain: Chain<Val, ()>
  ) -> Res<()> {

    // Break forward edges from `rep` and retrieve kids.
    let kids = match self.map_for.remove(rep) {
      Some(kids) => kids,
      None => return Err(
        vec![
          format!("[insert_chain] rep {} has no kids in the graph", rep)
        ]
      ),
    } ;

    // Break backward edges from `rep` and retrieve parents.
    let to_update = match self.map_bak.remove(rep) {
      Some(parents) => parents,
      None => return Err(
        vec![
          format!("[insert_chain] rep {} has no parents in the graph", rep)
        ]
      ),
    } ;

    let mut stack = vec![ (chain, kids, to_update) ] ;

    // Inserting in the parents.
    loop {

      match stack.pop() {

        // No chain to insert. Link the reps to update to the kids above.
        Some( (Chain::Nil, kids, set) ) => for parent in set.into_iter() {
          try_str!(
            self.add_kids_ref(& parent, & kids),
            "[insert_chain] while linking on an empty chain"
          )
        },

        Some( (chain, kids, mut set) ) => {

          // Chain is not empty. Anything in the set?
          let parent = set.iter().next().map(|parent| parent.clone()) ;

          if let Some(parent) = parent {
            // Removing parent and pushing the set back on the stack.
            set.remove(& parent) ;
            stack.push( (chain.clone(), kids.clone(), set.clone()) ) ;
            // Retrieving the value of the parent.
            let parent_value = match self.values.get(& parent) {
              Some(v) => v.clone(),
              None => return Err(
                vec![
                  format!("[insert_chain] parent {} has no value", parent)
                ]
              ),
            } ;

            // `unwrap` can't fail here, chain's not empty.
            let (top_value, top_rep) = chain.top_value().unwrap() ;

            // Can we insert anything above this parent?
            if parent_value <= top_value {
              // Link kids to top rep.
              try_str!(
                self.add_kids(& top_rep, kids),
                "[insert_chain] while adding kids to top rep {} (1)", top_rep
              ) ;
              // Longest chain to insert above this parent.
              let (above, chain) = chain.split_at(& parent_value) ;
              debug_assert!( above.len() > 0 ) ;

              let mut kids = TermSet::new() ;
              // Can't fail, `chain` can't be empty.
              kids.insert( above[0].clone() ) ;
              // Link parent to last rep of the chain.
              try_str!(
                self.add_kids( & parent, kids.clone() ),
                "[insert_chain] while adding kids to parent {} (1)", parent
              ) ;
              // Iterate on the rest of the chain if it's not empty.
              if ! chain.is_empty() {
                stack.push((
                  chain,
                  kids,
                  try_str!(
                    self.parents_of(& parent),
                    "[insert_chain] while retrieving parents of parent {} (1)",
                    parent
                  ).clone()
                ))
              }

            } else {
              // Nothing to insert above. Link kids to parent and to top.
              try_str!(
                self.add_kids_ref(& parent, & kids),
                "[insert_chain] while adding kids to parent {} (2)", parent
              ) ;
              try_str!(
                self.add_kids(& top_rep, kids),
                "[insert_chain] while adding kids to top rep {} (2)", top_rep
              ) ;
              stack.push(
                (
                  chain,
                  TermSet::new(),
                  try_str!(
                    self.parents_of(& parent),
                    "[insert_chain] while retrieving parents of parent {} (2)",
                    parent
                  ).clone()
                )
              )
            }

          } else {
            // Nothing left to update, move on to the rest of the stack.
            ()
          }
        },

        None => break,
      }

    }

    Ok(())
  }

  /** Stabilizes the whole graph for a model given as an evaluator. */
  pub fn split(& mut self, eval: & mut Eval<Val>) -> Res<()> {
    // INVARIANT: a class can be split **iff** all its parents have already
    //            been split.

    // Clear `values` memory.
    self.values.clear() ;

    println!("stabilizing...") ;

    println!("  retrieving orphans...") ;

    // Get all orphan representatives.
    let mut to_do = TermSet::with_capacity(self.classes.len() / 2) ;
    for (rep, parents) in self.map_bak.iter() {
      if parents.is_empty() {
        let _ = to_do.insert(rep.clone()) ;
        ()
      }
    } ;

    for orphan in to_do.iter() {
      println!("    - {}", orphan)
    }

    // Stabilization loop.
    'to_do: loop {

      // If there's something in `to_do`, work on that. Otherwise `break`.
      let rep = match to_do.iter().next() {
        Some(next) => next.clone(),
        None => break 'to_do
      } ;
      println!("  splitting {}", rep) ;
      // Remove `rep` from to_do as we're gonna handle it.
      to_do.remove(& rep) ;

      // Split equivalence class.
      let chain = try_strs!(
        self.split_class(& rep, eval),
        "[split] while splitting rep {}", rep
      ) ;
      // Insert resulting chain.
      try_strs!(
        self.insert_chain(& rep, chain),
        "[split] while inserting chain after splitting rep {}", rep
      ) ;

      // Add kids of `rep` to `to_do` and loop.
      let kids = try_str!(
        self.kids_of(& rep),
        "[split] while retrieving the kids of rep {}", rep
      ) ;
      for kid in kids.iter() {
        let _ = to_do.insert(kid.clone()) ;
        ()
      }

    }

    println!("done") ;

    Ok(())
  }

}
