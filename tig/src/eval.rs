// Copyright 2015 Adrien Champion. See the COPYRIGHT file at the top-level
// directory of this distribution.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use std::collections::HashMap ;
use std::marker::PhantomData ;

use term::{ Offset2, Cst, Term, Factory, Model } ;

use graph::{ Key, Val } ;


/** Cached evaluator.

For big systems, the cache of the evaluator can grow quite big. Note that we
always evaluate the same set of terms, hence its size is the same between
iterations.

Ideally we want to allocate it, reach the max capacity, and reuse that cache
when evaluating over a different model to avoid re-allocating it. That's why
the workflow is to create one evaluator and then recycle it:

`let evaluator = Eval::mk(model_1, offset_1, factory) ;`

Do stuff, and later just recycle.

`evaluator.recycle(new_model, new_offset) ;`
*/
pub struct Eval<V: Val> {
  /// Phantom data for the type we evaluate things to.
  phantom: PhantomData<V>,
  /// The model we're evaluating with.
  model: Model,
  /// The offset we're evaluating with.
  offset: Offset2,
  /// The cache for term evaluation in this model.
  cache: HashMap<Key, Cst>,
  /// Term factory for actual evaluation.
  factory: Factory,
}
impl<V: Val> Eval<V> {
  /** Builds a new evaluator. Only call once, then call `recycle` for optimal
  cache allocation. */
  pub fn mk(model: Model, offset: Offset2, factory: Factory) -> Self {
    Eval {
      phantom: PhantomData,
      model: model, offset: offset,
      cache: HashMap::with_capacity(100), factory: factory
    }
  }

  /** Resets the evaluator with a new model. The cache is reset but its
  capacity is kept. */
  pub fn recycle(& mut self, model: Model, offset: Offset2) {
    self.model = model ;
    self.offset = offset ;
    self.cache.clear() ;
    ()
  }

  /// Evaluates a term, cached.
  pub fn eval(& mut self, term: Term) -> Result<V, String> {
    use term::zip::Step ;
    let mut stack = vec![] ;       // Vector of `Step`s for zipping down/up.
    let mut values  = vec![] ;     // Vector of arguments already evaluated.
    let mut current = vec![term] ; // Vector of terms for current arguments.

    loop {

      'eval_args: loop {

        if let Some(term) = current.pop() {
          // There is a term to evaluate for this step.

          if let Some(cst) = self.cache.get(& term.hkey()) {
            // Cache hit, done with this term.
            values.push(cst.clone())

          } else {
            use term::real_term::Term::* ;
            // Need to evaluate this term.
            match * term.get() {
              // Variable, evaluate.
              V(_) => match self.factory.eval(
                & term, & self.offset, & self.model
              ) {
                Ok(c) => values.push(c),
                Err(s) => return Err(s),
              },

              // Constant, nothing to do.
              C(ref cst) => values.push(cst.clone()),

              // Operator, putting on stack.
              Op(ref op, ref args) => {
                use std::iter::Extend ;
                stack.push(
                  (
                    Step::Op(op.clone(), vec![()]),
                    values, current
                  )
                ) ;
                values = Vec::with_capacity(args.len()) ;
                current = Vec::with_capacity(args.len()) ;
                current.extend( args.iter().map(|t| t.clone()) )
              },

              App(ref sym, _) => panic!(
                format!("evaluation of applications not implemented ({})", sym)
              ),

              Let(_, _) => panic!(
                "evaluation of let bindings not implemented"
              ),

              Forall(_, _) | Exists(_, _) => panic!(
                "evaluation of quantifier not implemented"
              ),
            }
          }
        } ;

        if current.is_empty() {
          // Done evaluating the arguments of whatever step we're in.
          // Going up now.
          break 'eval_args
        }
      }

      // Going up. There should no term to evaluate.
      debug_assert!( current.is_empty() ) ;

      if let Some( (step, vals, curs) ) = stack.pop() {
        // Stack's not empty.
        match step {

          Step::Op(op, _) => {
            // Evaluating operator on arguments.
            let val = match op.eval(& self.factory, values) {
              Ok(val) => val,
              Err(s) => return Err(s),
            } ;
            // Restoring previous context.
            values = vals ;
            current = curs ;
            // Pushing new value to context.
            values.push(val)
          },

          _ => panic!("aaa"),
        }
      } else {
        // Stack is empty, there should be exactly one value in `values` and no
        // term in `current`. We're done.
        debug_assert!(  values.len() == 1 ) ;
        debug_assert!( current.is_empty() ) ;
        let val = values.pop().unwrap() ;
        return V::eval_cst(
          & val, & self.offset, & self.model, & self.factory
        )
      }
    }
  }
}