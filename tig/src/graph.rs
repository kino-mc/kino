// Copyright 2016 Adrien Champion. See the COPYRIGHT file at the top-level
// directory of this distribution.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

/*! Graph representing the knowledge learnt by the invariant generation
technique. */

use std::io ;

use common::Res ;
use common::msg::Event ;
use common::conf ;

use term::{
  Factory, Term, TermSet, TermMap
} ;
use term::tmp::{ TmpTerm, TmpTermSet, TmpTermMap } ;

use system::Sys ;

use Domain ;
use eval::Eval ;
use chain::* ;
use lsd::* ;


/// The graph structure, storing the nodes and the edges.
pub struct Graph<Val: Domain> {
  /// System the graph's for.
  sys: Sys,
  /// Forward edges between representatives.
  map_for: TermMap<TermSet>,
  /// Backward edges between representatives.
  map_bak: TermMap<TermSet>,
  /// Maps representatives to their class.
  classes: TermMap<TermSet>,
  /// Remembers which classes have already been stabilized.
  /// Stores the representatives.
  memory: TermSet,
  /// Stores the representatives that have been split and their value.
  values: TermMap<Val>,
}

impl<Val: Domain> Graph<Val> {

  /// Checks the graph's consistency.
  #[cfg(not(release))]
  fn check(& self, blah: & str) -> bool {
    if self.map_for.len() != self.map_bak.len() {
      panic!(
        "[{}] inconsistent size map_for ({}) and map_bak ({})",
        blah, self.map_for.len(), self.map_bak.len()
      )
    }
    for (rep, kids) in self.map_for.iter() {
      for kid in kids.iter() {
        match self.map_bak.get(kid) {
          None => panic!("could not retrieve parents of {}", kid),
          Some(kid_parents) => if ! kid_parents.contains(rep) {
            panic!(
              "[{}] found {} -> {} in map_for, but not in map_bak",
              blah, rep, kid
            )
          },
        }
      }
    }
    for (rep, parents) in self.map_bak.iter() {
      for parent in parents.iter() {
        match self.map_for.get(parent) {
          None => panic!("could not retrieve parents of {}", parent),
          Some(parent_kids) => if ! parent_kids.contains(rep) {
            panic!(
              "[{}] found {} -> {} in map_for, but not in map_bak",
              blah, parent, rep
            )
          },
        }
      }
    }
    true
  }

  /// Checks the graph's consistency.
  #[cfg(release)]
  #[inline(always)]
  fn check(& self, blah: & str) -> bool {
    true
  }

  /// Creates an empty graph.
  #[inline]
  fn with_capacity(capa: usize, sys: Sys) -> Self {
    Graph {
      sys: sys,
      map_for: TermMap::with_capacity( capa ),
      map_bak: TermMap::with_capacity( capa ),
      classes: TermMap::with_capacity( capa ),
      memory:  TermSet::with_capacity( capa ),
      values:  TermMap::with_capacity( capa ),
    }
  }

  /// Creates a new graph from a unique equivalence class.
  #[inline]
  pub fn mk(sys: & Sys, rep: Term, class: TermSet) -> Self {
    // Creating empty graph.
    let mut graph = Graph::with_capacity(class.len() / 3, sys.clone()) ;
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

  /// Minimal set of candidate invariants the graph represents.
  pub fn candidates<
    Ignore: Fn(& TmpTerm) -> bool
  >(& self, ignore: Ignore) -> TmpTermSet {
    let mut set = TmpTermSet::with_capacity( self.classes.len() * 5 ) ;
    for (ref rep, ref class) in self.classes.iter() {
      for term in class.iter() {
        // println!("  {} = {}", rep, term) ;
        Val::insert_eq(rep, term, & mut set, & ignore)
      }
    }
    // println!("") ;
    for (ref rep, ref kids) in self.map_for.iter() {
      for kid in kids.iter() {
        Val::insert_cmp(rep, kid, & mut set, & ignore)
      }
    }
    set
  }

  /// All candidate invariants the graph represents.
  pub fn all_candidates<
    Ignore: Fn(& TmpTerm) -> bool
  >(& self, ignore: Ignore) -> Res<TmpTermSet> {
    let mut set = TmpTermSet::with_capacity( self.classes.len() * 5 ) ;
    for (ref rep, ref class) in self.classes.iter() {
      let mut class = class.iter() ;
      while let Some(term) = class.next() {
        // Equality with rep.
        Val::insert_eq(rep, term, & mut set, & ignore) ;
        // Equality with other terms.
        for other_term in class.clone() {
          Val::insert_eq(term, other_term, & mut set, & ignore)
        }
      }
    }
    for (ref rep, ref kids) in self.map_for.iter() {
      let class = try_str_opt!(
        self.classes.get(rep),
        "[Graph::all_candidates] could not retrieve class of rep {}", rep
      ) ;
      for kid in kids.iter() {
        let kid_class = try_str_opt!(
          self.classes.get(kid),
          "[Graph::all_candidates] could not retrieve class of rep {}", rep
        ) ;
        // Comparison rep/kid.
        Val::insert_cmp(rep, kid, & mut set, & ignore) ;
        // Comparison rep/kid_class.
        for kid in kid_class.iter() {
          Val::insert_cmp(rep, kid, & mut set, & ignore)
        }
        // Rest.
        for parent in class.iter() {
          Val::insert_cmp(parent, kid, & mut set, & ignore) ;
          for kid in kid_class.iter() {
            Val::insert_cmp(parent, kid, & mut set, & ignore)
          }
        }
      }
    }
    Ok(set)
  }

  /// Isolates a representative. Returns the old kids and parents of the rep.
  pub fn isolate(& mut self, rep: & Term) -> Res<(TermSet, TermSet)> {
    let kids = if let Some( kids ) = self.map_for.remove(rep) {
      self.map_for.insert(rep.clone(), TermSet::new()) ;
      for kid in kids.iter() {
        if let Some( kid_parents ) = self.map_bak.get_mut(kid) {
          let was_there = kid_parents.remove(rep) ;
          debug_assert!( was_there )
        } else {
          return Err(
            format!(
              "[isolate] unknown kid {} of rep {} in `map_bak`", kid, rep
            )
          )
        }
      }
      kids
    } else {
      return Err(
        format!("[isolate] unknown rep {} in `map_for`", rep)
      )
    } ;

    let parents = if let Some( parents ) = self.map_bak.remove(rep) {
      self.map_bak.insert(rep.clone(), TermSet::new()) ;
      for parent in parents.iter() {
        if let Some( parent_kids ) = self.map_for.get_mut(parent) {
          let was_there = parent_kids.remove(rep) ;
          debug_assert!( was_there )
        } else {
          return Err(
            format!(
              "[isolate] unknown parent {} of rep {} in `map_for`", parent, rep
            )
          )
        }
      }
      parents
    } else {
      return Err(
        format!("[isolate] unknown rep {} in `map_bak`", rep)
      )
    } ;

    Ok( (kids, parents) )
  }

  /// Adds a single kid to a representative.
  pub fn add_kid_ref(
    & mut self, rep: Term, kid: & Term
  ) -> () {
    // println!("      linking {} to {}", rep, kid) ;
    let to_insert = match self.map_bak.get_mut(kid) {
      // Add parent to parents.
      Some(set) => {
        let _ = set.insert(rep.clone()) ;
        None
      },
      // Add parent as new set.
      None => {
        let mut set = TermSet::new() ;
        set.insert(rep.clone()) ;
        Some(set)
      },
    } ;
    if let Some(to_insert) = to_insert {
      self.map_bak.insert(kid.clone(), to_insert) ;
    }

    // Add backward edge if `rep` is not in `map_bak`.
    if ! self.map_bak.contains_key(& rep) {
      self.map_bak.insert(rep.clone(), TermSet::new()) ;
      ()
    }

    // Update forward edges.
    let set = if let Some(mut set) = self.map_for.remove(& rep) {
      set.insert(kid.clone()) ;
      set
    } else {
      let mut set = TermSet::new() ;
      set.insert( kid.clone() ) ;
      set
    } ;
    // Add the new kids.
    self.map_for.insert(rep.clone(), set) ;

    self.check("check, add_kid") ;

    ()
  }

  /// Adds kids to a representative. Updates `map_for` and `map_bak`.
  pub fn add_kids(
    & mut self, rep: & Term, kids: TermSet
  ) -> () {
    // if ! kids.is_empty() {
    //   println!("      linking {} to", rep) ;
    //   for kid in kids.iter() {
    //     println!("      - {}", kid)
    //   }
    // }
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

    // Add backward edge if `rep` is not in `map_bak`.
    if ! self.map_bak.contains_key(rep) {
      self.map_bak.insert(rep.clone(), TermSet::new()) ;
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
      None => {
        self.map_for.insert(rep.clone(), kids) ;
        ()
      },
    }

    self.check("check, add_kids") ;

    ()
  }

  /// Adds kids to a representative. Updates `map_for` and `map_bak`.
  ///
  /// Version where `kids` is a reference.
  pub fn add_kids_ref(
    & mut self, rep: & Term, kids: & TermSet
  ) -> Res<()> {
    // if ! kids.is_empty() {
    //   println!("      linking {} to", rep) ;
    //   for kid in kids.iter() {
    //     println!("      - {}", kid)
    //   }
    // }
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

    // Add backward edge if `rep` is not in `map_bak`.
    if ! self.map_bak.contains_key(rep) {
      self.map_bak.insert(rep.clone(), TermSet::new()) ;
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

    self.check("check add_kids_ref") ;

    Ok(())
  }

  /// Length of `map_for`, `map_bak`, and `classes`.
  pub fn lens(& self) -> (usize, usize, usize) {
    (self.map_for.len(), self.map_bak.len(), self.classes.len())
  }

  /// Dumps a graph as dot to a file. Also runs dot to the generate the PDF.
  pub fn dot_dump(& self, path: & str) -> Res<()> {
    use std::fs::File ;
    use std::process::Command ;
    let mut file = try_str!(
      File::create(path),
      "could not create file {}", path
    ) ;
    try_str!(
      self.dot_fmt(& mut file),
      "could not dump graph as dot in file {}", path
    ) ;
    let mut child = try_str!(
      Command::new("dot").arg("-Tpdf").arg("-o").arg(
        & format!("{}.pdf", path)
      ).arg(path).spawn(),
      "could not spawn `dot` command"
    ) ;
    let ecode = try_str!(
      child.wait(),
      "while running `dot` command"
    ) ;
    if ecode.success() {
      Ok(())
    } else {
      let mut err = format!("`dot` command failed:") ;
      if let Some( stderr ) = child.stderr {
        use std::io::{ BufReader, BufRead } ;
        let reader = BufReader::new(stderr) ;
        for line in reader.lines() {
          let line = try_str!(
            line,
            "{}\n[< could not retrieve line of stdout >]", err
          ) ;
          err = format!("{}\n{}", err, line)
        }
        Err(err)
      } else {
        Err(
          format!("{}\n[< could not retrieve stdout of process >]", err)
        )
      }
    }
  }

  /// Formats a graph in dot format.
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
    try!(
      write!(
        w,
        "  \
  node [
    style=filled
    fillcolor=black
    fontcolor=\"#1e90ff\"
    color=\"#66FF66\"
  ] ;
  edge [color=\"#FF9090\" fontcolor=\"#222222\"] ;

\
        "
      )
    ) ;

    // Printing classes.
    for (rep, class) in self.classes.iter() {
      let rep_value = match self.values.get(rep) {
        Some(v) => format!("{}", v),
        None => format!("_"),
      } ;
      try!(
        write!(
          w,
          "  \
            \"{} ({})\" -> \"\
          ",
          rep, rep_value
        )
      ) ;
      let mut first = true ;
      for term in class.iter() {
        let pref = if first {
          first = false ;
          ""
        } else { "\\n" } ;
        try!(
          write!(w, "{}{}", pref, term)
        )
      }
      try!( write!(w, "\" ;\n") )
    }

    write!(w, "}}\n")
  }

  /// Class corresponding to a representative.
  #[inline]
  pub fn class_of<'a, 'b>(
    & 'a self, rep: & 'b Term
  ) -> Result<& 'a TermSet, String> {
    match self.classes.get(rep) {
      Some(set) => Ok(set),
      None => Err(
        format!("[Graph::class_of] representative `{}` is unknown", rep)
      ),
    }
  }

  /// Class corresponding to a representative (mutable version).
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

  /// Kids corresponding of a representative.
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

  /// Kids corresponding to a representative (mutable version).
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

  /// Returns true iff all the parents of a rep are valued, except `term`.
  #[inline]
  pub fn has_valued_parents_except(
    & self, rep: & Term, term: & Term
  ) -> Result<bool, String> {
    match self.map_bak.get(rep) {
      Some(parents) => {
        for parent in parents.iter() {
          if parent != term && ! self.values.contains_key(parent) {
            return Ok(false)
          }
        }
        Ok(true)
      },
      None => Err(
        format!(
          "[Graph::has_valued_parents] representative {} is unknown", rep
        )
      ),
    }
  }

  /// Parents corresponding of a representative.
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

  /// Parents corresponding to a representative (mutable version).
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

  /// Clears the stabilization memory. Call before starting a stabilization
  /// step.
  #[inline]
  pub fn clear_memory(& mut self) {
    self.memory.clear()
  }

  /// Removes a term from a class corresponding to a representative.
  pub fn drop_member(
    & mut self, rep: & Term, elem: & Term
  ) -> Res<bool> {
    // Getting the right equivalence class. */
    let class = try_str!(
      self.class_mut_of(rep),
      "[drop_member] retrieving class of {}", rep
    ) ;
    // Removing element.
    Ok( class.remove(elem) )
  }

  /// Splits a class corresponding to a representative, given an evaluator.
  ///
  /// Returns a chain.
  ///
  /// Only modifies the `classes` and `values` fields of the graph to break
  /// `rep`'s class and create the ones encoded in the final chain, and update
  /// the values of the different representatives.
  pub fn split_class(
    & mut self, rep: & Term, eval: & mut Eval<Val>
  ) -> Res< Chain<Val, ()> > {
    // Starting with an empty chain.
    let mut chain = Chain::nil() ;
    
    {
      let class = match self.classes.get(rep) {
        Some(class) => class,
        None => return Err(
          format!("[split_class] representative {} is unknown", rep)
        ),
      } ;
      // Evaluate representative first.
      chain = try_str!(
        chain.insert(
          try_str!(
            eval.eval_term(rep),
            "[split_class] while evaluating representative"
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
              eval.eval_term(term),
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
        // println!("    values.insert({}, {})", rep, v) ;
        let _ = graph.values.insert(rep.clone(), v) ;
        let _ = graph.classes.insert(rep, set) ;
        ()
      },
      self
    ) ;
    // Return the chain.
    Ok(chain)
  }

  /// Inserts a chain in a graph.
  pub fn insert_chain(
    & mut self, rep: & Term, chain: Chain<Val, ()>
  ) -> Res<()> {
    if chain.is_empty() {
      return Err(
        format!("cannot insert an empty chain")
      )
    }

    let (kids, to_update) = try_str!(
      self.isolate(rep), "while link breaking"
    ) ;

    // // Break forward edges from `rep` and retrieve kids.
    // let kids = match self.map_for.remove(rep) {
    //   Some(kids) => {
    //     self.map_for.insert(rep.clone(), TermSet::new()) ;

    //     kids
    //   },
    //   None => return Err(
    //     format!("[insert_chain] rep {} has no kids in the graph", rep)
    //   ),
    // } ;

    // // Break backward edges from `rep` and retrieve parents.
    // let to_update = match self.map_bak.remove(rep) {
    //   Some(parents) => {
    //     self.map_bak.insert(rep.clone(), TermSet::new()) ;
    //     parents
    //   },
    //   None => return Err(
    //     format!("[insert_chain] rep {} has no parents in the graph", rep)
    //   ),
    // } ;

    // self.check("check, link breaking") ;

    // Create links between elements of the chain.
    let _ = chain.fold(
      (& mut * self, None),
      |(mut graph, prev), _, rep, _| {
        if let Some(prev) = prev {
          graph.add_kid_ref((* rep).clone(), & prev)
        } else {
          graph.add_kids(rep, TermSet::new() )
        }
        (graph, Some(rep.clone()))
      }
    ) ;

    let last_of_chain = chain.last().unwrap().1.clone() ;

    let mut stack = vec![ (chain, kids, to_update) ] ;

    // Inserting in the parents.
    loop {

      match stack.pop() {

        // No chain to insert. Link the reps to update to the kids above.
        Some( (Chain::Nil, kids, set) ) => {
          // println!("  - chain: []") ;
          // println!("    kids:  {:?}", kids) ;
          // println!("    set:   {:?}", set) ;
          for parent in set.into_iter() {
            try_str!(
              self.add_kids_ref(& parent, & kids),
              "[insert_chain] while linking on an empty chain"
            )
          }
        },

        Some( (chain, kids, mut set) ) => {
          // println!("  - chain: {}", chain) ;
          // println!("    kids:  {:?}", kids) ;
          // println!("    set:   {:?}", set) ;
          // Chain is not empty. Anything in the set?
          let parent = set.iter().next().map(|parent| parent.clone()) ;

          // `unwrap`-s can't fail here, chain's not empty.
          let (top_value, top_rep) = chain.top_value().unwrap() ;

          if let Some(parent) = parent {
            // println!("    parent: {}", parent) ;
            // Removing parent and pushing the set back on the stack.
            set.remove(& parent) ;
            stack.push( (chain.clone(), kids.clone(), set.clone()) ) ;
            // Retrieving the value of the parent.
            let parent_value = match self.values.get(& parent) {
              Some(v) => v.clone(),
              None => return Err(
                format!("[insert_chain] parent {} has no value", parent)
              ),
            } ;

            // Can we insert anything above this parent?
            if parent_value <= top_value {
              // println!("    parent value above top value") ;
              // Link kids to top rep.
              self.add_kids(& top_rep, kids) ;
              // Longest chain to insert above this parent.
              let (above, chain) = chain.split_at(& parent_value) ;
              // println!("    above: {:?}", above) ;
              debug_assert!( above.len() > 0 ) ;

              let mut kids = TermSet::new() ;
              // Can't fail, `chain` can't be empty.
              kids.insert( above[0].clone() ) ;
              // Link parent to last rep of the chain.
              // println!("    parent to last rep") ;
              self.add_kid_ref( parent.clone(), & above[0] ) ;
              // Iterate on the rest of the chain if it's not empty.
              if ! chain.is_empty() {
                // println!("    chain below is not empty") ;
                stack.push((
                  chain,
                  kids,
                  try_str!(
                    self.parents_of(& parent),
                    "[insert_chain] while retrieving parents of parent {} (1)",
                    parent
                  ).clone()
                ))
              } else {
                // println!("    chain below is empty") ;
                self.add_kid_ref(parent, & last_of_chain)
              }

            } else {
              // println!("    parent value below top value") ;
              // Nothing to insert above. Link kids to parent and to top.
              try_str!(
                self.add_kids_ref(& parent, & kids),
                "[insert_chain] while adding kids to parent {} (2)", parent
              ) ;
              self.add_kids(& top_rep, kids) ;
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
            // println!("    no parent") ;
            self.add_kids(& top_rep, kids) ;
            // Nothing left to update, move on to the rest of the stack.
            ()
          }
        },

        None => break,
      }

    }

    Ok(())
  }

  /// Orphan representatives in the graph.
  pub fn orphans(& self) -> TermSet {
    let mut orphans = TermSet::with_capacity(self.classes.len() / 2) ;
    for (rep, parents) in self.map_bak.iter() {
      if parents.is_empty() {
        let wasnt_there = orphans.insert( rep.clone() ) ;
        debug_assert!( wasnt_there )
      }
    }
    orphans
  }

  /// Stabilizes the whole graph for a model given as an evaluator.
  pub fn split(& mut self, eval: & mut Eval<Val>) -> Res<()> {
    // INVARIANT: a class can be split **iff** all its parents have already
    //            been split.
    // This is forced by starting from orphan nodes in the graph, splitting
    // them, and then iterating on their kids.

    // Clear `values` memory.
    self.values.clear() ;

    // println!("stabilizing...") ;

    // println!("  retrieving orphans ({:?})...", self.lens()) ;

    // Get all orphan representatives.
    let mut to_do = self.orphans() ;

    // for orphan in to_do.iter() {
    //   println!("    - {}", orphan)
    // }

    // Stabilization loop.
    'to_do: loop {

      // println!("todo:") ;
      // for to_do in to_do.iter() {
      //   println!("- {}", to_do)
      // }

      // If there's something in `to_do`, work on that. Otherwise `break`.
      let rep = match to_do.iter().next() {
        Some(next) => next.clone(),
        None => break 'to_do
      } ;

      // Add kids of `rep` to `to_do`.
      {
        let kids = try_str!(
          self.kids_of(& rep),
          "[split] while retrieving the kids of rep {}", rep
        ) ;
        for kid in kids.iter() {
          if try_str!(
            self.has_valued_parents_except(kid, & rep),
            "[split] while checking if kid {} has valued parents", kid
          ) {
            to_do.insert(kid.clone()) ;
            ()
          }
        }
      }

      // println!("  splitting {}", rep) ;
      // Remove `rep` from to_do as we're gonna handle it.
      to_do.remove(& rep) ;

      // Split equivalence class.
      let chain = try_str!(
        self.split_class(& rep, eval),
        "[split] while splitting rep {}", rep
      ) ;
      // println!("    {}", chain) ;
      // Insert resulting chain.
      try_str!(
        self.insert_chain(& rep, chain),
        "[split] while inserting chain after splitting rep {}", rep
      ) ;

    }

    // println!("done") ;

    Ok(())
  }

}


/// Partial graph stabilizer.
///
/// The query scheme for this graph is different than that over the complete
/// graph. Here, each class is looked at separately. If it is falsifiable, we
/// get a model and stabilize the whole graph with it.
///
/// If it is not falsifiable, then it is stable and we extract the actual
/// invariants from the class. Then, we check if the class has any parents and
/// stabilize the edges with the parents, before identifying the actual
/// invariants in the edges too.
///
/// It is safe to do this because of the functional invariant of the approach:
/// > **We try to stabilize a class iff all its parents are already stable.**
pub struct PartialGraph<Val: Domain> {
  /// The complete graph.
  graph: Graph<Val>,
  /// The representatives of the stable equivalence classes.
  stable: TermSet,
  /// Factory, for `TmpTerm` transformation.
  factory: Factory,
  /// Previous candidate invariants to check again.
  candidates: TmpTermMap< Option< (Term, Term) > >,
  /// Activates early eq invariant discovery.
  early_eqs: bool,
  /// Activates early cmp invariant discovery.
  early_cmps: bool,
}
impl<Val: Domain> PartialGraph<Val> {
  /// Creates a partial graph stabilizer from a graph.
  #[inline]
  pub fn of(
    factory: & Factory, graph: Graph<Val>, conf: & conf::Tig
  ) -> Self {
    // let orphans = graph.orphans() ;
    PartialGraph {
      graph: graph,
      stable: TermSet::with_capacity(17),
      factory: factory.clone(),
      candidates: TmpTermMap::with_capacity(209),
      early_eqs: * conf.early_eqs(),
      early_cmps: * conf.early_cmps(),
    }
  }

  /// Prepares the partial graph for a new stabilization phase.
  #[inline]
  pub fn clear(& mut self) {
    self.stable.clear() ;
    self.candidates.clear() ;
  }

  /// Extracts a representative from `self.to_do`.
  #[inline]
  fn get_next(& mut self) -> Option<Term> {
    // let next = match self.to_do.iter().next() {
    //   Some(next) => next.clone(),
    //   None => return None,
    // } ;
    // let was_there = self.to_do.remove(& next) ;
    // debug_assert!( was_there ) ;
    // Some(next)

    // Look for unstable rep with stable parents.
    'rep_loop: for (rep, parents) in self.graph.map_bak.iter() {
      // Skip if stable.
      if self.stable.contains(rep) { continue 'rep_loop }
      // Inspect parents.
      'parent_loop: for parent in parents.iter() {
        // Skip the rep if parent's not stable.
        if ! self.stable.contains(parent) { continue 'rep_loop }
      }
      // Reachable only if all parents are stable.
      return Some( rep.clone() )
    }
    // Reachable only if no unstable rep has all its parents stable (graph is
    // stable).
    return None
  }

  /// Terms for the equality chain between members of a class.
  ///
  /// None if class is a singleton.
  fn base_terms_of_class(& self, rep: & Term, known: & mut TmpTermSet) -> Res<
    Option< Vec<TmpTerm> >
  > {
    if let Some(class) = self.graph.classes.get(rep) {
      // Early return if class is empty.
      if class.is_empty() {
        return Ok( None )
      }

      let mut terms = Vec::with_capacity(class.len()) ;
      for term in class.iter() {
        if let Some(eq) = Val::mk_eq(rep, term) {
          if ! known.contains(& eq) { terms.push( eq ) }
        }
      }
      Ok( Some(terms) )

    } else {
      Err(
        format!(
          "[PartialGraph::base_terms_of_class] \
          unknown rep `{}`", rep
        )
      )
    }
  }

  /// Candidate terms encoding all equalities between members of a class.
  ///
  /// Actually depends on the cardinality of `rep`'s class. If it's too big,
  /// then only equalities with the representative are produced.
  ///
  /// Each candidate term is mapped to a pair `(rep, term)` with the semantics
  /// that if a candidate term is invariant, then `term` can be dropped from
  /// the class of `rep`.
  ///
  /// Returns true iff some new candidates were generated.
  fn step_terms_of_class(
    & mut self, rep: & Term, known: & mut TmpTermSet
  ) -> Res<bool> {
    let rep_class = try_str!(
      self.graph.class_of(rep),
      "[PartialGraph::step_terms_of_class] \
      while retrieving class of `{}`", rep
    ) ;
    // Early return if class is empty.
    if rep_class.is_empty() {
      return Ok( false )
    }

    let generate_all = rep_class.len() <= 7 ;

    let mut iter = rep_class.iter() ;
    // Generate all terms.
    while let Some(term) = iter.next() {
      if let Some(eq) = Val::mk_eq(rep, term) {
        if ! known.contains(& eq) {
          let previous = self.candidates.insert(
            eq, Some( (rep.clone(), term.clone()) )
          ) ;
          debug_assert!( previous.is_none() )
        }
      }
      if generate_all {
        for trm in iter.clone() {
          if let Some(eq) = Val::mk_eq(term, trm) {
            if ! known.contains(& eq) {
              let previous = self.candidates.insert(
                eq, Some( (rep.clone(), trm.clone()) )
              ) ;
              debug_assert!( previous.is_none() )
            }
          }
        }
      }
    }
    Ok( true )
  }

  /// Terms for the relations between a representative and its parents.
  ///
  /// None if rep has no parents.
  fn base_terms_of_edges(& self, rep: & Term, known: & mut TmpTermSet) -> Res<
    Option< Vec<TmpTerm> >
  > {
    let parents = try_str_opt!(
      self.graph.map_bak.get(rep),
      "[PartialGraph::base_terms_of_edges] \
      unknown rep `{}`", rep
    ) ;

    // Early return if class is empty.
    if parents.is_empty() {
      return Ok( None )
    }

    let mut terms = Vec::with_capacity(parents.len()) ;
    for parent in parents.iter() {
      // println!("; | {} -> {}\n; |", parent, rep) ;
      if let Some(cmp) = Val::mk_cmp(parent, rep) {
        if ! known.contains(& cmp) {
          terms.push( cmp )
        }
      }
    }
    Ok(
      if ! terms.is_empty() {
        Some(terms)
      } else {
        None
      }
    )
  }

  /// Candidate terms encoding all edges between members of a class.
  ///
  /// Actually depends on the cardinality of `rep`'s class, and that of its
  /// parents. When a class is too big, then it is ignored and only edges
  /// from/to the representative are considered.
  ///
  /// Candidate terms are mapped to `()` since we don't want to remember
  /// anything about them. Info is for equivalences, where we can drop one a
  /// term from the class.
  fn step_terms_of_edges(
    & mut self, rep: & Term, known: & mut TmpTermSet
  ) -> Res<bool> {
    self.candidates.clear() ;
    let rep_parents = try_str!(
      self.graph.parents_of(rep),
      "[PartialGraph::step_terms_of_edges] \
      while retrieving parents of `{}`", rep
    ) ;
    let rep_class = try_str!(
      self.graph.class_of(rep),
      "[PartialGraph::step_terms_of_edges] \
      while retrieving class of `{}`", rep
    ) ;
    // Early return if no parents.
    if rep_parents.is_empty() {
      return Ok( false )
    }

    let rep_generate_all = rep_class.len() <= 7 ;

    // Generate all terms.
    for parent in rep_parents.iter() {
      // `parent => rep`
      // println!("; | (1) {} => {}\n; |", parent, rep) ;
      if let Some(cmp) = Val::mk_cmp(parent, rep) {
        if ! known.contains(& cmp) {
          let previous = self.candidates.insert(cmp, None) ;
          debug_assert!( previous.is_none() )
        }
      }
      for term in rep_class.iter() {
        // `parent => term`
        // println!("; | (2) {} => {}\n; |", parent, term) ;
        if let Some(cmp) = Val::mk_cmp(parent, term) {
          if ! known.contains(& cmp) {
            let previous = self.candidates.insert(cmp, None) ;
            debug_assert!( previous.is_none() )
          }
        }
      }
      let parent_class = try_str!(
        self.graph.class_of(parent),
        "[PartialGraph::step_terms_of_edges] \
        while retrieving class of `{}`, parent of `{}`", parent, rep
      ) ;

      let parent_generate_all = parent_class.len() <= 10 ;

      for parent_term in parent_class.iter() {
        // `parent_term => rep`
        // println!("; | (3) {} => {}\n; |", parent_term, rep) ;
        if let Some(cmp) = Val::mk_cmp(parent_term, rep) {
          if ! known.contains(& cmp) {
            let previous = self.candidates.insert(cmp, None) ;
            debug_assert!( previous.is_none() )
          }
        }

        if rep_generate_all && parent_generate_all {
          for term in rep_class.iter() {
            // `parent_term => term`
            // println!("; | (4) {} => {}\n; |", parent_term, term) ;
            if let Some(cmp) = Val::mk_cmp(parent_term, term) {
              if ! known.contains(& cmp) {
                let previous = self.candidates.insert(cmp, None) ;
                debug_assert!( previous.is_none() )
              }
            }
          }
        }
      }
    }
    Ok( true )
  }

  /// Returns all the step terms for the graph. Equivalent to calling
  /// `step_terms_of_class` and `step_terms_of_edges` on all classes.
  fn step_terms(
    & mut self, known: & mut TmpTermSet
  ) -> Res<bool> {
    let mut set = TermSet::with_capacity( self.graph.classes.len() ) ;
    for (ref rep, _) in self.graph.classes.iter() {
      set.insert( (* rep).clone() ) ;
    }
    let mut new_stuff = false ;
    for rep in set.into_iter() {
      new_stuff = new_stuff || try_str!(
        self.step_terms_of_class(& rep, known),
        "[PartialGraph::step_terms] on the class of rep `{}`", rep
      ) ;
      new_stuff = new_stuff || try_str!(
        self.step_terms_of_edges(& rep, known),
        "[PartialGraph::step_terms] on the edges of rep `{}`", rep
      )
    }
    Ok( new_stuff )
  }

  /// `k`-splits some candidates using a step solver. Handles communication
  /// too.
  pub fn k_split<Base, Step>(
    & mut self, base: & mut Base, step: & mut Step,
    known: & mut TmpTermSet, event: & mut Event
  ) -> Res<()>
  where Base: BaseTrait<Val, Step>, Step: StepTrait<Val, Base> {
    use common::msg::MsgDown ;
    use term::{ STerm, STermSet, UnTermOps } ;

    match event.recv() {
      None => (),
      Some(msgs) => for msg in msgs {
        match msg {
          MsgDown::Forget(_, _) => (),
          MsgDown::Invariants(sym, invs) => if self.graph.sys.sym() == & sym  {
            // event.log(
            //   & format!("received {} invariants", invs.len())
            // ) ;
            // event.log( & format!("add_invs [{}, {}]", check_offset, k) ) ;
            try_str!(
              base.add_invs(invs.clone()),
              "[PartiaGraph::k_split] \
              while adding invariants from supervisor to base at {}",
              base.unroll_len()
            ) ;
            try_str!(
              step.add_invs(invs),
              "[PartiaGraph::k_split] \
              while adding invariants from supervisor to step at {}",
              step.unroll_len()
            ) ;
          },
          _ => event.error("unknown message"),
        }
      },
    }

    self.graph.check("before k-split") ;

    let invars = try_str!(
      step.k_split(& mut self.candidates),
      "[PartialGraph::k_split] step query"
    ) ;

    if ! invars.is_empty() {
      let mut set = STermSet::with_capacity(invars.len()) ;
      for (invar, info) in invars.into_iter() {
        if let Some( (rep, to_drop) ) = info {
          try_str!(
            self.graph.drop_member(& rep, & to_drop),
            "[PartialGraph::k_split] \
            while dropping `{}` from the class of `{}`", to_drop, rep
          ) ;
        }
        let wasnt_there = known.insert(invar.clone()) ;
        debug_assert!(wasnt_there) ;
        let invar = try_str!(
          invar.to_term_safe(& self.factory),
          "[PartialGraph::k_split] while building one-state invariant"
        ) ;
        let wasnt_there = set.insert(
          STerm::One(
            try_str!(
              self.factory.debump(& invar),
              "[PartialGraph::k_split] while building one-state invariant"
            ),
            invar
          )
        ) ;
        debug_assert!( wasnt_there )
      } ;
      event.invariants_at( self.graph.sys.sym(), set, base.unroll_len() )
    }
    Ok(())
  }

  /// Looks for invariants in the whole graph.
  pub fn k_split_all<Base, Step>(
    & mut self, base: & mut Base, step: & mut Step,
    known: & mut TmpTermSet, event: & mut Event
  ) -> Res<()>
  where Base: BaseTrait<Val, Step>, Step: StepTrait<Val, Base> {
    self.candidates.clear() ;
    let new_stuff = try_str!(
      self.step_terms(known),
      "[PartialGraph::k_split_all] during step term extraction"
    ) ;
    if new_stuff {
      // use std::time::Instant ;
      // let cand_count = self.candidates.len() ;
      // event.log(
      //   & format!(
      //     "k-splitting {} candidates from {} classes",
      //     cand_count, self.graph.classes.len()
      //   )
      // ) ;
      // let start = Instant::now() ;
      let res = self.k_split(base, step, known, event) ;
      // let time = Instant::now() - start ;
      // event.log(
      //   & format!(
      //     "done k-splitting {} candidates in {}.{} seconds",
      //     cand_count, time.as_secs(), time.subsec_nanos()
      //   )
      // ) ;
      res
    } else { Ok(()) }
  }

  /// Stabilizes an equivalence class, extracts invariants.
  /// **Communicates invariants itself.** Returns `true` iff the graph is
  /// stable in base.
  ///
  /// Once the class is stable, extracts invariants. Then, stabilizes all
  /// edges leading to this class, and extracts invariants once it's done.
  ///
  /// # TO DO
  ///
  /// Make `k_split`ting a loop so that it builds on the invariants it finds.
  pub fn stabilize_next_class<
    Base, Step, GraphLog: Fn(& Graph<Val>, & str, & str) -> Res<()>
  >(
    & mut self, base: & mut Base, step: & mut Step, event: & mut Event,
    known: & mut TmpTermSet, graph_log: & GraphLog, tag: String,
  ) -> Res< bool >
  where Base: BaseTrait<Val, Step>, Step: StepTrait<Val, Base> {
    use common::msg::MsgDown ;
    use std::time::Instant ;

    debug_assert!( base.unroll_len() + 1 >= step.unroll_len() ) ;

    debug_assert!(
      self.graph.check(
        "[PartialGraph::stabilize_next_class] original graph"
      )
    ) ;

    let mut next = match self.get_next() {
      Some(next) => next,
      None => return Ok(true),
    } ;

    // event.log(
    //   & format!("starting base eq stabilization from `{}`", next)
    // ) ;

    try_str!(
      graph_log(& self.graph, & tag, "0"),
      "could not dump graph as dot"
    ) ;

    match event.recv() {
      None => (),
      Some(msgs) => for msg in msgs {
        match msg {
          MsgDown::Forget(_, _) => (),
          MsgDown::Invariants(sym, invs) => if self.graph.sys.sym() == & sym  {
            // event.log(
            //   & format!("received {} invariants", invs.len())
            // ) ;
            // event.log( & format!("add_invs [{}, {}]", check_offset, k) ) ;
            try_str!(
              base.add_invs(invs.clone()),
              "while adding invariants from supervisor to base at {}",
              base.unroll_len()
            ) ;
            try_str!(
              step.add_invs(invs),
              "while adding invariants from supervisor to step at {}",
              step.unroll_len()
            ) ;
          },
          _ => event.error("unknown message"),
        }
      },
    }

    self.graph.check("before partial eq stabilization") ;

    let time_start = Instant::now() ;

    // Stabilize the graph class by class until one is stable.
    'base_eq: loop {

      let to_check = if let Some(to_check) = try_str!(
        self.base_terms_of_class(& next, known),
        "[PartialGraph::stabilize_next_class] \
        while getting eq base terms of `{}`", next
      ) {
        to_check
      } else {
        // event.log(
        //   & format!("`{}` is alone, moving on", next)
        // ) ;
        break 'base_eq
      } ;

      // event.log(
      //   & format!("partial-eq-stabilizing, {} terms", to_check.len())
      // ) ;

      let eval_opt = try_str!(
        base.k_falsify(to_check),
        "[PartialGraph::stabilize_next_class] \
        during `k_falsify` query for eqs of `{}`", next
      ) ;

      if let Some(mut eval) = eval_opt {
        // event.log("class is not stable, splitting") ;
        try!( self.graph.split(& mut eval) ) ;
        next = try_str_opt!(
          self.get_next(),
          "[PartialGraph::stabilize_next_class] \
          graph was just split for eqs but no next rep found"
        )
      } else {
        // event.log("class is stable, moving on") ;
        break 'base_eq
      }

    }
    // At this point, `next` is the representative of a stable class with
    // stable parents.

    try_str!(
      graph_log(& self.graph, & tag, "1"),
      "could not dump graph as dot"
    ) ;

    debug_assert!(
      self.graph.check(
        "[PartialGraph::stabilize_next_class] after eq stabilization"
      )
    ) ;

    match event.recv() {
      None => (),
      Some(msgs) => for msg in msgs {
        match msg {
          MsgDown::Forget(_, _) => (),
          MsgDown::Invariants(sym, invs) => if self.graph.sys.sym() == & sym  {
            // event.log(
            //   & format!("received {} invariants", invs.len())
            // ) ;
            // event.log( & format!("add_invs [{}, {}]", check_offset, k) ) ;
            try_str!(
              base.add_invs(invs.clone()),
              "while adding invariants from supervisor to base at {}",
              base.unroll_len()
            ) ;
            try_str!(
              step.add_invs(invs),
              "while adding invariants from supervisor to step at {}",
              step.unroll_len()
            ) ;
          },
          _ => event.error("unknown message"),
        }
      },
    }

    self.graph.check("before eq invariant extraction") ;

    let time_base_eq = Instant::now() ;

    // Extract invariant from the equivalence class of `next`.
    self.candidates.clear() ;
    if self.early_eqs && try_str!(
      self.step_terms_of_class(& next, known),
      "[PartialGraph::stabilize_next_class] \
      while preparing `k_split` eq query over rep `{}`", next
    ) {
      try_str!(
        self.k_split(base, step, known, event),
        "[PartialGraph::stabilize_next_class] \n\
        during `k_split` eq query over rep `{}`", next
      )
    } ;

    match event.recv() {
      None => (),
      Some(msgs) => for msg in msgs {
        match msg {
          MsgDown::Forget(_, _) => (),
          MsgDown::Invariants(sym, invs) => if self.graph.sys.sym() == & sym  {
            // event.log(
            //   & format!("received {} invariants", invs.len())
            // ) ;
            // event.log( & format!("add_invs [{}, {}]", check_offset, k) ) ;
            try_str!(
              base.add_invs(invs.clone()),
              "while adding invariants from supervisor to base at {}",
              base.unroll_len()
            ) ;
            try_str!(
              step.add_invs(invs),
              "while adding invariants from supervisor to step at {}",
              step.unroll_len()
            ) ;
          },
          _ => event.error("unknown message"),
        }
      },
    }

    // try_str!(
    //   base.restart(), "while restarting base at {}", base.unroll_len()
    // ) ;
    // try_str!(
    //   step.restart(), "while restarting step at {}", step.unroll_len()
    // ) ;

    // Stabilize the graph until the edges between `next` and its parents are
    // stable.

    // event.log(
    //   & format!("stabilizing edges leading to `{}`", next)
    // ) ;

    self.graph.check(
      "[PartialGraph::stabilize_next_class] after eq invariant extraction"
    ) ;

    let time_step_eq = Instant::now() ;

    'base_cmp: loop {

      // event.log(
      //   & format!("partial-cmp-stabilizing `{}`", next)
      // ) ;

      let to_check = if let Some(to_check) = try_str!(
        self.base_terms_of_edges(& next, known),
        "[PartialGraph::stabilize_next_class] \
        while getting cmp base terms of `{}`", next
      ) {
        to_check
      } else {
        // event.log(
        //   & format!("`{}` has no non-trivial parents, moving on", next)
        // ) ;
        break 'base_cmp
      } ;

      // event.log(
      //   & format!("partial-cmp-stabilizing, {} terms", to_check.len())
      // ) ;

      let eval_opt = try_str!(
        base.k_falsify(to_check),
        "[PartialGraph::stabilize_next_class] \
        during `k_falsify` query for cmps of `{}`", next
      ) ;

      if let Some(mut eval) = eval_opt {
        // event.log("edges are not stable, splitting") ;
        try!( self.graph.split(& mut eval) )
      } else {
        // event.log("edges are stable, moving on") ;
        break 'base_cmp
      }

    }
    // At this point, all edges leading to `next` are stable.

    try_str!(
      graph_log(& self.graph, & tag, "0"),
      "could not dump graph as dot"
    ) ;

    self.graph.check(
      "[PartialGraph::stabilize_next_class] after cmp stabilization"
    ) ;

    match event.recv() {
      None => (),
      Some(msgs) => for msg in msgs {
        match msg {
          MsgDown::Forget(_, _) => (),
          MsgDown::Invariants(sym, invs) => if self.graph.sys.sym() == & sym  {
            // event.log(
            //   & format!("received {} invariants", invs.len())
            // ) ;
            // event.log( & format!("add_invs [{}, {}]", check_offset, k) ) ;
            try_str!(
              base.add_invs(invs.clone()),
              "while adding invariants from supervisor to base at {}",
              base.unroll_len()
            ) ;
            try_str!(
              step.add_invs(invs),
              "while adding invariants from supervisor to step at {}",
              step.unroll_len()
            ) ;
          },
          _ => event.error("unknown message"),
        }
      },
    }

    let time_base_cmp = Instant::now() ;

    // Extract invariant from the edges leading `next`.
    self.candidates.clear() ;
    if self.early_cmps && try_str!(
      self.step_terms_of_edges(& next, known),
      "[PartialGraph::stabilize_next_class] \
      while preparing `k_split` cmp query over rep `{}`", next
    ) {
      try_str!(
        self.k_split(base, step, known, event),
        "[PartialGraph::stabilize_next_class] \n\
        during `k_split` cmp query over rep `{}`", next
      )
    } ;

    let time_step_cmp = Instant::now() ;

    let (_t_1, _t_2, _t_3, _t_4) = (
      time_base_eq - time_start,
      time_step_eq - time_base_eq,
      time_base_cmp - time_step_eq,
      time_step_cmp - time_base_cmp
    ) ;

    // event.log(
    //   & format!(
    //     "stats:\n  \
    //     base eq:  {:>4}.{}\n  \
    //     step eq:  {:>4}.{}\n  \
    //     base cmp: {:>4}.{}\n  \
    //     step cmp: {:>4}.{}\n",
    //     t_1.as_secs(), t_1.subsec_nanos(),
    //     t_2.as_secs(), t_2.subsec_nanos(),
    //     t_3.as_secs(), t_3.subsec_nanos(),
    //     t_4.as_secs(), t_4.subsec_nanos(),
    //   )
    // ) ;

    let wasnt_there = self.stable.insert(next) ;
    debug_assert!( wasnt_there ) ;

    self.graph.check(
      "[PartialGraph::stabilize_next_class] after cmp invariant extraction"
    ) ;

    Ok(false)
  }

}