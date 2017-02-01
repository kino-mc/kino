/*! *Temporary* terms that are not hashconsed.

Typically used for activation literals and conjunction of properties. */

use std::collections::{ HashSet, HashMap } ;
use std::fmt ;

use rsmt2::Expr2Smt ;
use errors::* ;
use super::{
  Term, Type, Operator, Offset2
} ;

use Factory ;

/// A set of temporary terms.
pub type TmpTermSet = HashSet<TmpTerm> ;
/// A map from temporary terms to something.
pub type TmpTermMap<Val> = HashMap<TmpTerm, Val> ;

/** *Temporary* terms that are not hashconsed.

**Warning**: no `|`-quoting is added when printing a symbol in SMT-LIB 2. */
#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub enum TmpTerm {
  /// A (typed) symbol.
  Sym(String, Type),
  /// A normal (hashconsed) term.
  Trm(Term),
  /// A node: an operator and some kids.
  Nod(Operator, Vec<TmpTerm>),
}

impl TmpTerm {
  /// The symbols in the temporary layer of a temporary term.
  pub fn get_syms(& self) -> HashSet<(String, Type)> {
    use self::TmpTerm::* ;
    let mut res = HashSet::with_capacity(5) ;
    let mut stack = Vec::with_capacity(7) ;
    stack.push(self) ;

    while let Some(term) = stack.pop() {
      match * term {
        Sym(ref id, ref ty) => {
          let _ = res.insert( (id.clone(), * ty) ) ;
        },
        Trm(_) => (),
        Nod(_, ref kids) => for kid in kids.iter() {
          stack.push(kid)
        },
      }
    }

    res.shrink_to_fit() ;
    res
  }

  /// Transforms a temp term in a normal term.
  ///
  /// Returns an error if the temp term contains a `Sym`. That's because
  /// a symbol in a temp term is a temporary symbol. There is currently no
  /// situation where a temporary symbol needs to be converted to a term.
  pub fn to_term_safe(mut self, factory: & Factory) -> Res<Term> {
    use term::OpMaker ;
    use self::TmpTerm::* ;

    // Temp terms are supposed to be relatively shallow, small stack.
    //
    // Stores triples of
    // - an operator
    // - a list of terms
    // - a list of temp terms
    let mut stack = Vec::with_capacity(4) ;

    // Inserts a term in a stack.
    //
    // Result is either `Union::Lft` with the final term, meaning the stack
    // has been consumed. Or a `Union::Rgt` containing the next temp term to
    // translate.
    let insert = |
      stack: & mut Vec< (Operator, Vec<Term>, Vec<TmpTerm>) >,
      mut term,
      factory: & Factory
    | {
      loop {
        if let Some( (op, mut kids, mut to_do) ) = stack.pop() {
          kids.push(term) ;
          match to_do.pop() {
            // No terms left for this node, going up.
            None => term = factory.op(op, kids),
            // There's some temp kids left, done.
            Some(tmp_kid) => {
              stack.push( (op, kids, to_do) ) ;
              return Union::Rgt(tmp_kid)
            },
          }
        } else {
          // Stack's empty, we done.
          return Union::Lft(term)
        }
      }
    } ;

    loop {

      match self {

        // Already a real term, insert in stack.
        Trm(t) => match insert(& mut stack, t, factory) {
          // Insertion yields the result term.
          Union::Lft(result) => {
            debug_assert!( stack.len() == 0 ) ;
            return Ok(result)
          },
          // Insertion yields the next temp term to translate.
          Union::Rgt(t) => self = t,
        },

        // Node, updating `stack` and `term`.
        Nod(op, mut kids) => {
          // Reverse kids so that it's in the right order in the stack.
          kids.reverse() ;
          // Retrieving first kid.
          self = if let Some(kid) = kids.pop() { kid } else {
            let e: Res<Term> = Err(
              ErrorKind::OpArityError(op, 0, "> 1").into()
            ) ;
            return e.chain_err(
              || ErrorKind::TmpTransError
            )
          } ;
          // Updating stack.
          stack.push(
            (op, Vec::with_capacity( kids.len() ), kids)
          )
        },

        // Symbols are illegal.
        Sym(s, t) => {
          let e: Res<Term> = Err(
            format!(
              "temporary term contains a symbol {} ({})", s, t
            ).into()
          ) ;
          return e.chain_err(
            || "conversion to actual term is unsafe and \
              should not be needed anyway"
          ).chain_err(
            || ErrorKind::TmpTransError
          )
        },
      }
    }
  }

  /// Creates a conjunction of temp terms.
  pub fn and(terms: Vec<TmpTerm>) -> TmpTerm {
    TmpTerm::Nod( Operator::And, terms )
  }

  /// Creates a conjunction of real terms.
  pub fn mk_term_conj(terms: & Vec<Term>) -> TmpTerm {
    TmpTerm::and(
      terms.iter().map(|t| TmpTerm::Trm(t.clone())).collect()
    )
  }

  /// Creates an implication between two real terms.
  pub fn mk_term_impl(lhs: Term, rhs: Term) -> TmpTerm {
    TmpTerm::Nod(
      Operator::Impl,
      vec![ TmpTerm::Trm(lhs), TmpTerm::Trm(rhs) ]
    )
  }

  /// Creates an `Le` relation between two real terms.
  pub fn mk_term_le(lhs: Term, rhs: Term) -> TmpTerm {
    TmpTerm::Nod(
      Operator::Le,
      vec![ TmpTerm::Trm(lhs), TmpTerm::Trm(rhs) ]
    )
  }

  /// Creates an `Eq` relation between two real terms.
  pub fn mk_term_eq(lhs: Term, rhs: Term) -> TmpTerm {
    TmpTerm::Nod(
      Operator::Eq,
      vec![ TmpTerm::Trm(lhs), TmpTerm::Trm(rhs) ]
    )
  }

  /// Inspects a term to write it. Pushes to the input stack if the term
  /// is a node.
  fn inspect_write_stack(
    & self, writer: & mut ::std::io::Write, offset: & Offset2,
    stack: & mut Vec< Vec<TmpTerm> >
  ) -> ::rsmt2::errors::Res<()> {
    use self::TmpTerm::* ;
    match * self {
      Sym(ref id, _) => smt_cast_io!(
        format!("writing id `{}`", id) => write!(writer, "{}", id)
      ),
      Trm(ref term) => term.expr_to_smt2(writer, offset),
      Nod(ref op, ref kids) => {
        use write::Writable ;
        let mut kids = kids.clone() ;
        kids.reverse() ;
        smtry_io!(
          format!("writing opening for operator `{}`", op) =>
            write!(writer, "(") ;
            op.write(writer) ;
        ) ;
        stack.push( kids ) ;
        Ok(())
      },
    }
  }
}

impl fmt::Display for TmpTerm {
  fn fmt(& self, fmt: & mut fmt::Formatter) -> fmt::Result {
    let mut stack = vec![ ( vec![self], "", "" ) ] ;
    while let Some( (mut kids, sep, end) ) = stack.pop() {
      if let Some(kid) = kids.pop() {
        use self::TmpTerm::* ;
        stack.push( (kids, sep, end) ) ;
        match * kid {
          Sym(ref s, _) => try!( write!(fmt, "{}{}", sep, s) ),
          Trm(ref trm) => try!( write!(fmt, "{}{}", sep, trm) ),
          Nod(ref op, ref kids) => {
            try!( write!(fmt, "{}({}", sep, op) ) ;
            let mut keeds = Vec::with_capacity(kids.len()) ;
            for kid in kids.iter() {
              keeds.push(kid)
            }
            stack.push( (keeds, " ", ")") )
          },
        }
      } else {
        try!( write!(fmt, "{}", end) )
      }
    }
    Ok(())
  }
}

impl Expr2Smt<Offset2> for TmpTerm {
  fn expr_to_smt2(
    & self, writer: & mut ::std::io::Write, offset: & Offset2
  ) -> ::rsmt2::errors::Res<()> {
    let mut stack = Vec::with_capacity(5) ;
    try!(
      self.inspect_write_stack(writer, offset, & mut stack)
    ) ;

    while let Some(mut kids) = stack.pop() {
      if let Some(term) = kids.pop() {
        stack.push(kids) ;
        smtry_io!(
          format!("writing expressions `{}` with offset `{}`", self, offset) =>
            write!(writer, " ") ;
            term.inspect_write_stack(writer, offset, & mut stack) ;
        )
      } else {
        smtry_io!(
          format!(
            "writing closing paren for expressions `{}`", self
          ) => write!(writer, ")")
        )
      }
    }

    Ok(())
  }
}

/// Helper enum for term translation.
pub enum Union<T1, T2> {
  /// A value of the first type.
  Lft(T1),
  /// A value of the second type.
  Rgt(T2),
}

/// Can create an activation term from something.
pub trait TmpTermMker {
  /// Creates an actlit for something implying something.
  #[inline]
  fn under_actlit(self, String) -> TmpTerm ;
  /// Creates a negation.
  #[inline]
  fn tmp_neg(self) -> TmpTerm ;
}

impl<'a, T: TmpTermMker + Clone> TmpTermMker for & 'a T {
  #[inline]
  fn under_actlit(self, id: String) -> TmpTerm {
    self.clone().under_actlit(id)
  }
  #[inline]
  fn tmp_neg(self) -> TmpTerm {
    self.clone().tmp_neg()
  }
}

impl TmpTermMker for TmpTerm {
  #[inline]
  fn under_actlit(self, id: String) -> TmpTerm {
    TmpTerm::Nod(
      Operator::Impl, vec![
        TmpTerm::Sym(id, Type::Bool),
        self
      ]
    )
  }
  #[inline]
  fn tmp_neg(self) -> TmpTerm {
    TmpTerm::Nod( Operator::Not, vec![self] )
  }
}

impl TmpTermMker for Term {
  #[inline]
  fn under_actlit(self, id: String) -> TmpTerm {
    TmpTerm::Trm(self).under_actlit(id)
  }
  #[inline]
  fn tmp_neg(self) -> TmpTerm {
    TmpTerm::Trm(self).tmp_neg()
  }
}