// Copyright 2015 Adrien Champion. See the COPYRIGHT file at the top-level
// directory of this distribution.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

/*! Term generator. 

Guaranteed to produce different terms each time it is asked to generate terms.

# Usage

A generator is created by giving a map from types to terms. The generator will
use these terms to create more when `generate` is called.
*/

use std::collections::HashMap ;
use std::fmt ;

pub use rand::* ;

use super::* ;

/** Can generate random terms. */
pub struct TermGen<Rand> {
  /** RNG. */
  rng: Rand,
  /** Terms generated so far. */
  generated: HashMap<Type, TermSet>,
  /** Factory. */
  factory: Factory,
}

impl TermGen<isaac::IsaacRng> {
  /** Builds a new generator from a seed. Uses Isaac RNG. */
  pub fn of_seed(
    factory: Factory, init: HashMap<Type, TermSet>, seed: & [u32]
  ) -> Self {
    TermGen {
      rng: isaac::IsaacRng::from_seed(seed),
      generated: init,
      factory: factory,
    }
  }

  /** Builds a new generator using a fixed seed. Uses Isaac RNG. */
  pub fn of(factory: Factory, init: HashMap<Type, TermSet>) -> Self {
    TermGen {
      rng: isaac::IsaacRng::from_seed(
        & [
          2u32, 3u32, 5u32, 7u32,
          11u32, 13u32, 17u32,
          19u32, 23u32, 29u32,
          31u32, 37u32, 41u32,
          43u32, 47u32, 53u32,
          59u32, 61u32, 67u32,
          71u32, 73u32, 79u32,
          83u32, 89u32, 97u32,
        ]
      ),
      generated: init,
      factory: factory,
    }
  }
}

impl TermGen<ThreadRng> {
  /** Builds a random generator. */
  pub fn random(factory: Factory, init: HashMap<Type, TermSet>) -> Self {
    TermGen {
      rng: thread_rng(),
      generated: init,
      factory: factory,
    }
  }
}

impl<Rand: Rng> TermGen<Rand> {

  /** Builds a new generator from a `RNG`. */
  pub fn of_rng(
    factory: Factory, init: HashMap<Type, TermSet>, rng: Rand
  ) -> Self {
    TermGen {
      rng: rng, generated: init, factory: factory,
    }
  }

  /** Generates `n` random terms of type `typ`. The optional `max_depth`
  argument is maximal number of layers on top of the terms given during the
  creation of the term generator. */
  pub fn generate(
    & mut self, typ: Type, n: usize, max_depth: Option<usize>
  ) -> TermSet {
    let mut constructor = Zip::mk(
      typ, & mut self.generated, & mut self.rng, & self.factory
    ) ;
    let mut terms = TermSet::with_capacity(n) ;
    for _ in 0..n {
      terms.insert(
        constructor.build(max_depth)
      ) ;
    } ;
    terms
  }
}


// |===| Helper functions and structures for random term generation.

/** Can return the `n`th element of itself. */
trait CanNth<T> {
  /** The `n`th element of itself. */
  fn nth(& self, n: usize) -> T ;
}
impl CanNth<Term> for TermSet {
  fn nth(& self, n: usize) -> Term {
    let mut n = n % self.len() ;
    for t in self.iter() {
      if n == 0 { return t.clone() } else { n = n - 1 }
    } ;
    unreachable!()
  }
}

/** Returns true or false. True has `pc`% chances of being returned. */
fn rand_bool<Rand: Rng>(rng: & mut Rand, pc: u8) -> bool {
  rng.next_f32() <= (pc as f32) / 100f32
}

/** Returns a `usize` in the interval `[0,max[`. No bias. */
fn rand_int<Rand: Rng>(rng: & mut Rand, max: usize) -> usize {
  (rng.next_u64() as usize) % max
}

/** Returns a random bool to bool operator. */
fn rand_bool_to_bool<Rand: Rng + Sized>(rng: & mut Rand) -> Operator {
  use Operator::* ;
  // Distinct with 5%.
  if rand_bool(rng, 5) { Distinct } else {
    let ops = vec![ Eq, And, Or, Impl, Xor ] ;
    ops[ rand_int(rng, ops.len()) ]
  }
}

/** Returns a random arith to bool operator. */
fn rand_arith_to_bool<Rand: Rng + Sized>(rng: & mut Rand) -> Operator {
  use Operator::* ;
  // Distinct with 5%.
  if rand_bool(rng, 5) { Distinct } else {
    let ops = vec![ Eq, Le, Ge, Lt, Gt ] ;
    ops[ rand_int(rng, ops.len()) ]
  }
}

/** Returns a random arith to arith operator. */
fn rand_arith_to_arith<Rand: Rng + Sized>(rng: & mut Rand) -> Operator {
  use Operator::* ;
  let ops = vec![ Add, Sub, Neg, Mul, Div ] ;
  ops[ rand_int(rng, ops.len()) ]
}


/** Constructive zipper step. */
enum Step {
  /** Zipper is below the condition of an ite. */
  Ite0(Type),
  /** Zipper is below the then of an ite. */
  Ite1(usize, Term),
  /** Zipper is below the else of an ite. */
  Ite2(usize, Term, Term),
  /** We're below a let-binding. */
  Let,
  /** We're below an operator. */
  Op(Operator, Type, usize, Vec<Term>),
}

impl fmt::Display for Step {
  fn fmt(& self, fmt: & mut fmt::Formatter) -> fmt::Result {
    use self::Step::* ;
    match * self {
      Ite0(ref t) => write!(fmt, "Ite0({})", t),
      Ite1(ref d, ref t) => write!(fmt, "Ite1({})({})", d, t),
      Ite2(ref d, ref c, ref t) => write!(fmt, "Ite2({})({}, {})", d, c, t),
      Let => write!(fmt, "Let"),
      Op(ref op, ref t, ref d, ref terms) => {
        try!( write!(fmt, "Op({})( {}, {}, (", d, op, t) ) ;
        for t in terms.iter() {
          try!( write!(fmt, " {},", t) )
        } ;
        write!(fmt, ") )")
      }
    }
  }
}


/** Constructive zipper, holds the information for the construction of the
current term and moving upwards.*/
struct Zip<'a, Rand: 'a> {
  /** Path leading to the current term. */
  path: Vec<Step>,
  /** Type of the current term. */
  typ: Type,
  /** Sequence of bindings. */
  bindings: Vec< (HashMap<Type, Vec<Sym>>, Vec<(Sym, Term)>) >,
  /** Terms available. */
  terms: & 'a mut HashMap<Type, TermSet>,
  /** Depth associated to the terms.
  Does **not** correspond to the actual depth of the terms.

  Terms provided at creation of the generator are given depth zero. */
  depth: HashMap<Term, usize>,
  /** Max depth requested by the generation query.
  Stored in the structure to make things easier. */
  max_depth: Option<usize>,
  /** RNG. */
  rng: & 'a mut Rand,
  /** Factory. */
  factory: & 'a Factory,
  /** Can generate int terms. */
  can_int: bool,
  /** Can generate rat terms. */
  can_rat: bool,
  /** Can generate arith terms. */
  can_arith: bool,
  /** Index for fresh variables. */
  index: usize,
}

impl<'a, Rand: 'a + Rng + Sized> Zip<'a, Rand> {

  /** Creates a new constructive zipper for some type. */
  pub fn mk(
    typ: Type, terms: & 'a mut HashMap<Type, TermSet>,
    rng: & 'a mut Rand, factory: & 'a Factory
  ) -> Self {
    let (can_int, can_rat) = (
      match terms.get(& Type::Int) {
        None => false, Some(set) => set.len() > 0
      },
      match terms.get(& Type::Rat) {
        None => false, Some(set) => set.len() > 0
      },
    ) ;
    let mut depth = HashMap::with_capacity(terms.len()) ;
    for (_, set) in terms.iter() {
      for term in set {
        depth.insert(term.clone(), 0) ;
        ()
      }
    } ;
    Zip {
      path: Vec::with_capacity(107),
      typ: typ,
      bindings: Vec::with_capacity(5),
      terms: terms,
      depth: depth,
      max_depth: None,
      rng: rng,
      factory: factory,
      can_int: can_int,
      can_rat: can_rat,
      can_arith: can_int || can_rat,
      index: 0,
    }
  }

  /** Pushes a step. */
  fn push(& mut self, step: Step) { self.path.push(step) }

  /** Pops a step. */
  fn pop(& mut self) -> Option<Step> { self.path.pop() }

  /** Returns true for zippers at the top level (path has length 0). */
  fn at_top(& self) -> bool { self.path.len() == 0 }

  /** Returns true iff `bindings` is not empty. */
  fn below_let(& self) -> bool { ! self.bindings.is_empty() }

  /** Returns the depth of a zipper. */
  fn depth(& self) -> usize {
    self.path.len()
  }

  /** Returns the depth of a term. Fails if it is not defined. */
  fn depth_of(& self, t: & Term) -> usize {
    match self.depth.get(t) {
      Some(d) => * d,
      None => panic!(
        "[gen::zip] asked for depth of a term I don't know the depth of: {}",
        t
      ),
    }
  }

  /** Returns a term of type `typ` of depth less than `depth - max` if
  `max_depth = Some(max)`. Otherwise just returns a term of type `typ`.

  Also returns the depth of the term choosen. */
  fn get_term(& mut self, typ: Type) -> (Term, usize) {
    println!(
      "|   > get_term ({}/{})",
      self.depth(),
      match self.max_depth {
        None => 0,
        Some(max) => max,
      }
    ) ;
    match self.terms.get(& typ) {
      Some(term_set) => loop {
        // Get a random term of type `typ`.
        let term = term_set.nth(
          rand_int(& mut self.rng, term_set.len())
        ) ;
        // Check its depth.
        match self.depth.get(& term) {
          Some(d) => match self.max_depth {
            Some(max) => if self.depth() + d <= max {
              println!("|     done") ;
              // Less than max depth, returning this term.
              return (term, * d)
            } else {
              // Term's depth is too high, looping to get another one.
              continue
            },
            // No max depth, returning the term and its depth.
            None => {
              println!("|     done") ;
              return (term, * d)
            },
          },
          None => panic!(
            "[gen::zip] I don't know the depth of term {}", term
          ),
        }
      },
      None => panic!(
        "[gen::zip] asked for a term of type {}, \
        but no term of that type is available",
        typ
      ),
    }
  }

  /** Inserts a new binding. */
  fn insert_binding(& mut self, (sym, term): (Sym, Term)) -> Result<(),()> {
    if ! self.bindings.is_empty() {
      let last = self.bindings.len() - 1 ;
      let (ref mut map, ref mut vec) = self.bindings[last] ;
      vec.push( (sym.clone(), term) ) ;
      match map.get_mut(& self.typ) {
        None => (),
        Some(vec) => {
          vec.push(sym.clone()) ;
          return Ok(())
        },
      } ;
      let binding = vec![ sym ] ;
      map.insert(self.typ.clone(), binding) ;
      Ok(())
    } else {
      Err(())
    }
  }

  /** Returns a fresh variable. */
  fn fresh(& mut self) -> (Sym, Term) {
    let sym = self.factory.sym(
      format!("@fresh {}", self.index)
    ) ;
    self.index = self.index + 1 ;
    (sym.clone(), self.factory.var(sym))
  }

  /** Adds a term to the map from types to terms if we're not under a let
  binding. */
  fn remember(& mut self, term: Term) -> Option<bool> {
    let typ = self.typ ;
    // Remember only if we're not under a let binding.
    for & (ref map, _) in self.bindings.iter() {
      for (_, ref vec) in map.iter() {
        if ! vec.is_empty() { return None }
      }
    } ;
    match self.terms.get_mut(& typ) {
      Some(term_set) => {
        let was_there = term_set.insert(term) ;
        Some(was_there)
      },
      None => panic!(
        "[gen::zip] no candidate term set for type {}", self.typ
      ),
    }
  }

  /** Goes down, bool version. */
  fn bool_down(& mut self) {
    // Going down into arith at 10%.
    if self.can_arith && rand_bool(& mut self.rng, 10) {
      let typ = match (self.can_int, self.can_rat) {
        // Int or rat, 50%.
        (true, true) => if rand_bool(& mut self.rng, 50) {
          Type::Int
        } else {
          Type::Rat
        },
        // Can only int.
        (true, false) => Type::Int,
        // Can only rat.
        (false, true) => Type::Rat,
        _ => unreachable!(),
      } ;
      let op = rand_arith_to_bool(& mut self.rng) ;
      self.push( Step::Op(op, Type::Bool, 0, Vec::with_capacity(3) ) ) ;
      self.typ = typ
    } else {
      // Staying in bool.
      let op = rand_bool_to_bool(& mut self.rng) ;
      self.push( Step::Op(op, Type::Bool, 0, Vec::with_capacity(2)) ) ;
      // Type is still bool.
      ()
    }
  }

  /** Goes down, arith version. */
  fn arith_down(& mut self) {
    let op = rand_arith_to_arith(& mut self.rng) ;
    let typ = self.typ ;
    self.push( Step::Op(op, typ, 0, Vec::with_capacity(1)) )
  }

  /** Builds a random term. */
  pub fn build(& mut self, max_depth: Option<usize>) -> Term {
    self.max_depth = max_depth ;
    self.down()
  }

  /** Goes down a constructive zipper. */
  fn down(& mut self) -> Term {
    use self::Step::* ;

    loop {

      println!("|   > down ({})", self.depth()) ;

      let down_allowed = match self.max_depth {
        None => true,
        Some(d) => self.depth() < d,
      } ;

      // Generate a let binding with 5% chance.
      if down_allowed && rand_bool(& mut self.rng, 5) {
        self.push( Let ) ;
        self.bindings.push( (HashMap::new(), vec![]) )
      } else {

        // Generate an if then else with 5% chance.
        if down_allowed && rand_bool(& mut self.rng, 5) {
          let typ = self.typ ;
          self.push( Ite0(typ) ) ;
          self.typ = Type::Bool
        } else {

          // Reuse existing term if not at top level with 70% probability.
          if ! down_allowed || (
            ! self.at_top() && rand_bool(& mut self.rng, 70)
          ) {
            let typ = self.typ ;
            let (term, depth) = self.get_term(typ) ;
            match self.up(term, depth) {
              Some(term) => return term,
              None => (),
            }

          } else {
            // Otherwise generate new term.
            match self.typ {
              Type::Bool => self.bool_down(),
              Type::Int | Type::Rat => self.arith_down(),
            }
          }
        }
      }
    }
  }

  /** Goes up a constructive zipper. */
  fn up(& mut self, mut term: Term, mut depth: usize) -> Option<Term> {
    use std::cmp::max ;
    use self::Step::* ;

    loop {
      //    /\=======================================================/\
      //   /!!\ Do not use `continue` in this loop. The `depth` map /!!\
      //  /!!!!\          is updated at the end of it.             /!!!!\
      // /======\=================================================/======\

      // Let-bind if possible with probability 30%.
      if self.below_let() && rand_bool(& mut self.rng, 30) {
        let (f_sym, f_term) = self.fresh() ;
        self.insert_binding( (f_sym, term.clone()) ).unwrap() ;
        term = f_term
      } else {

        if let Some(step) = self.pop() {
          // Not a top, going up.
          term = match step {

            // Term is the condition of an if-then-else.
            Ite0(typ) => {
              assert_eq!(Type::Bool, self.typ) ;
              self.typ = typ ;
              self.push( Ite1(depth, term) ) ;
              return None
            },

            // Term is the then of an if-then-else.
            Ite1(old_depth, cond) => {
              self.push(
                Ite2(max(old_depth, depth), cond, term)
              ) ;
              return None
            },

            // Term is the else of an if-the-else.
            Ite2(old_depth, cond, then) => {
              let term = self.factory.ite(cond, then, term) ;
              depth = max(old_depth, depth) ;
              self.depth.insert( term.clone(), depth ) ;
              term
            },

            Let => {
              if let Some( (_, bindings) ) = self.bindings.pop() {
                if ! bindings.is_empty() {
                  for & (_, ref term) in bindings.iter() {
                    depth = max( depth, self.depth_of(term) )
                  } ;
                  self.factory.let_b(bindings, term)
                } else {
                  term
                }
              } else {
                panic!(
                  "[gen::zip] trying to construct let but no binding available"
                )
              }
            },

            Op(op, typ, old_depth, mut kids) => {
              kids.push(term) ;
              depth = max(old_depth, depth) ;
              match op.arity() {
                None => if kids.len() == 1 || rand_bool(& mut self.rng, 10) {
                  // Extend with 10% chance.
                  self.push(
                    Op(op, typ, depth, kids)
                  ) ;
                  return None
                } else {
                  // Otherwise go up.
                  self.typ = typ ;
                  self.factory.op(op, kids)
                },
                Some(n) if kids.len() < (n as usize) => {
                  // Not enough kids, going down.
                  self.push( Op(op, typ, depth, kids) ) ;
                  return None
                },
                Some(n) if kids.len() == (n as usize) => {
                  // Go up.
                  self.typ = typ ;
                  self.factory.op(op, kids)
                },
                _ => unreachable!(),
              }
            },
          } ;
          match self.remember(term.clone()) {
            Some(false) => (),
            // println!(
            //   "| [gen::zip::up] warning, already know {}", term
            // ),
            _ => (),
          }
        } else {
          // At top, done.
          return Some(term)
        }
      } ;
      self.depth.insert(term.clone(), depth) ;
      ()
    }
  }

}


