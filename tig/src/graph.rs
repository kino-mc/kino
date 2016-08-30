// Copyright 2015 Adrien Champion. See the COPYRIGHT file at the top-level
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
use std::collections::HashSet ;

use common::Res ;

use term::{
  Term, TermSet, TermMap,
} ;
use term::tmp::TmpTerm ;

use Domain ;
use eval::Eval ;
use chain::* ;


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

  /// Checks the graph's consistency.
  fn check(& self, blah: & str) -> () {
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
  }

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

  /// All candidate invariants the graph represents.
  pub fn candidates(& self) -> HashSet<TmpTerm> {
    let mut set = HashSet::with_capacity( self.classes.len() * 5 ) ;
    for (ref rep, ref class) in self.classes.iter() {
      for term in class.iter() {
        Val::insert_eq(rep, term, & mut set)
      }
    }
    for (ref rep, ref kids) in self.map_for.iter() {
      for kid in kids.iter() {
        Val::insert_cmp(rep, kid, & mut set)
      }
    }
    set
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

  /** Adds kids to a representative. Updates `map_for` and `map_bak`. */
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

  /** Adds kids to a representative. Updates `map_for` and `map_bak`.

  Version where `kids` is a reference. */
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
  edge [color=\"#FFFF66\" fontcolor=\"#222222\"] ;

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
        format!(
          "[drop_member] {} is not an element of the class of {}",
          elem, rep
        )
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

  /** Inserts a chain in a graph. */
  pub fn insert_chain(
    & mut self, rep: & Term, chain: Chain<Val, ()>
  ) -> Res<()> {

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

  /** Stabilizes the whole graph for a model given as an evaluator. */
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
    let mut to_do = TermSet::with_capacity(self.classes.len() / 2) ;
    for (rep, parents) in self.map_bak.iter() {
      // println!("looking at {}:", rep) ;
      // for parent in parents.iter() {
      //   println!("  - {}", parent)
      // }
      if parents.is_empty() {
        let _ = to_do.insert(rep.clone()) ;
        ()
      }
    } ;

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
