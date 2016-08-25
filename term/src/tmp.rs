/*! *Temporary* terms that are not hashconsed.

Typically used for activation literals and conjunction of properties. */

use std::collections::HashSet ;

use rsmt2::Expr2Smt ;
use super::{
  Term, Type, Operator, Offset2
} ;

/// *Temporary* terms that are not hashconsed.
#[derive(Clone)]
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

    res
  }

  /// Creates a conjunction of real terms.
  pub fn mk_term_conj(terms: & Vec<Term>) -> TmpTerm {
    TmpTerm::Nod(
      Operator::And,
      terms.iter().map(|t| TmpTerm::Trm(t.clone())).collect()
    )
  }

  /** Inspects a term to write it. Pushes to the input stack if the term
  is a node. */
  fn inspect_write_stack(
    & self, writer: & mut ::std::io::Write, offset: & Offset2,
    stack: & mut Vec< Vec<TmpTerm> >
  ) -> ::std::io::Result<()> {
    use self::TmpTerm::* ;
    match * self {
      Sym(ref id, _) => write!(writer, "{}", id),
      Trm(ref term) => term.expr_to_smt2(writer, offset),
      Nod(ref op, ref kids) => {
        use write::Writable ;
        let mut kids = kids.clone() ;
        kids.reverse() ;
        try!( write!(writer, "(") ) ;
        try!( op.write(writer) ) ;
        stack.push( kids ) ;
        Ok(())
      },
    }
  }
}

impl Expr2Smt<Offset2> for TmpTerm {
  fn expr_to_smt2(
    & self, writer: & mut ::std::io::Write, offset: & Offset2
  ) -> ::std::io::Result<()> {
    let mut stack = Vec::with_capacity(5) ;
    try!(
      self.inspect_write_stack(writer, offset, & mut stack)
    ) ;

    while let Some(mut kids) = stack.pop() {
      if let Some(term) = kids.pop() {
        stack.push(kids) ;
        try!( write!(writer, " ") ) ;
        try!( term.inspect_write_stack(writer, offset, & mut stack) ) ;
      } else {
        try!( write!(writer, ")") )
      }
    }

    Ok(())
  }
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