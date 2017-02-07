// Copyright 2015 Adrien Champion. See the COPYRIGHT file at the top-level
// directory of this distribution.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! System parsing.
//! 
//! ## To do
//! 
//! Context:
//! 
//! * hash of `Item` should be hash of its `Sym`, and replace hash maps with
//!   hash sets

static uf_desc:        & 'static str = "function declaration"         ;
static fun_desc:       & 'static str = "function definition"          ;
static prop_desc:      & 'static str = "property definition"          ;
static sys_desc:       & 'static str = "system definition"            ;
static check_desc:     & 'static str = "verify query"                 ;
static check_ass_desc: & 'static str = "verify with assumption query" ;

use std::io ;
use std::fmt ;
use std::sync::Arc ;
use std::time::Duration ;
use std::thread::sleep ;
use std::collections::{ HashSet, HashMap } ;

use term::{
  Type, Offset, Cst, Sym, Term, Factory, Model, STermSet
} ;
use term::parsing::* ;

use base::* ;
mod parsers ;
pub mod check ;
use self::check::Error ;

use self::parsers::* ;

fn map_to_lines<
  K: ::std::cmp::Eq + ::std::hash::Hash, V: fmt::Display
>(
  map: & HashMap<K, V>, title: & 'static str, mut acc: String
) -> String {
  acc = format!("{}\n{} {{", acc, title) ;
  if ! map.is_empty() {
    for (_, ref v) in map.iter() {
      acc = format!("{}\n  {}", acc, v)
    } ;
    format!("{}\n}}", acc)
  } else {
    format!("{}}}", acc)
  }
}

fn map_pairs_to_lines<
  K: ::std::cmp::Eq + ::std::hash::Hash, V: fmt::Display, W: fmt::Display
>(
  map: & HashMap<K, (V, W)>, title: & 'static str, mut acc: String
) -> String {
  acc = format!("{}\n{} {{", acc, title) ;
  if ! map.is_empty() {
    for (_, &(ref v, ref w)) in map.iter() {
      acc = format!("{}\n  {}: {}", acc, v, w)
    } ;
    format!("{}\n}}", acc)
  } else {
    format!("{}}}", acc)
  }
}

macro_rules! try_get {
  ($map:expr, $sym:expr, $id:ident => $b:block) => (
    match $map.get($sym) {
      None => (),
      Some($id) => return Some($b),
    }
  ) ;
  ($map:expr, $sym:expr, $e:expr) => (
    match $map.get($sym) {
      None => (),
      Some(_) => return Some($e),
    }
  ) ;
}

/// A positive or negative literal.
pub enum Atom {
  /// A positive literal.
  Pos( Spnd<Sym> ),
  /// A negative literal.
  Neg( Spnd<Sym> ),
}
impl Atom {
  #[inline]
  pub fn sym(& self) -> & Spnd<Sym> {
    match * self {
      Atom::Pos(ref sym) => sym,
      Atom::Neg(ref sym) => sym,
    }
  }
  #[inline]
  pub fn into_var(self, f: & Factory) -> Term {
    use term::VarMaker ;
    match self {
      Atom::Pos(sym) => {
        let (sym, _) = sym.destroy() ;
        f.var(sym)
      },
      Atom::Neg(sym) => {
        let (sym, _) = sym.destroy() ;
        f.not( f.var(sym) )
      },
    }
  }
}

/// Normal result of a parsing attempt.
#[derive(Debug)]
pub enum Res {
  /// Found an exit command.
  Exit,
  /// Found a check command.
  Check(::Sys, Vec<::Prop>),
  /// Found a check with assumptions command.
  CheckAss(::Sys, Vec<::Prop>, Vec<Term>)
}
impl Res {
  /// A multi-line representation of the result of a parsing attempty
  pub fn lines(& self) -> String {
    match * self {
      Res::Exit => "exit".to_string(),
      Res::Check(ref sys, ref props) => {
        let mut s = format!("verify {}", sys.sym()) ;
        for prop in props.iter() {
          s = format!("{}\n  {}", s, prop.sym())
        } ;
        s
      },
      Res::CheckAss(ref sys, ref props, ref atoms) => {
        let mut s = format!("verify {} (", sys.sym()) ;
        if ! props.is_empty() {
          for prop in props.iter() {
            s = format!("{}\n  {}", s, prop.sym())
          } ;
          s = format!("{}\n)", s)
        } else {
          s = format!("{})", s)
        } ;
        s = format!("{} assuming (", s) ;
        if ! atoms.is_empty() {
          for atom in atoms.iter() {
            s = format!("{}\n  {}", s, atom)
          } ;
          s = format!("{}\n)", s)
        } else {
          s = format!("{})", s)
        }
        s
      },
    }
  }
}

/// A counterexample for a system.
#[derive(Clone)]
pub struct Cex {
  sys: ::Sys,
  no_state: HashMap<Sym, Cst>,
  trace: HashMap<Offset, HashMap<Sym, Cst>>
}
impl Cex {
  /// Length of a cex. Number of states minus one.
  pub fn len(& self) -> usize {
    assert!(self.trace.len() > 0) ;
    self.trace.len() - 1
  }
  /// Formats a counterexample vmt-style.
  pub fn write_vmt<W: io::Write>(
    & self, props: & [ Sym ], fmt: & mut W
  ) -> io::Result<()> {
    try!( write!(fmt, "(cex\n  ( ") ) ;
    for prop in props.iter() {
      try!( write!(fmt, "{} ", prop) )
    }
    try!( write!(fmt, ")\n") ) ;

    // Printing function symbols.
    if self.no_state.is_empty() {
      try!( write!(fmt, "  () ; no function symbols\n") )
    } else {
      try!( write!(fmt, "  ( ; function symbols:") ) ;
      for (ref sym, ref cst) in self.no_state.iter() {
        try!(
          write!(
            fmt, "\n    (declare-fun {} () {} {})", sym, cst.typ(), cst
          )
        )
      }
      try!( write!(fmt, "\n  )\n") ) ;
    }

    // Printing states.
    let mut off = Offset::zero() ;
    while let Some( ref cex ) = self.trace.get(& off) {
      try!( write!(fmt, "  ; state {}:\n  (and\n", off) ) ;
      for (ref sym, ref cst) in cex.iter() {
        try!( write!(fmt, "    (= {} {})\n", sym, cst) )
      }
      try!( write!(fmt, "  )\n") ) ;
      off = off.nxt()
    }

    write!(fmt, ")\n")
  }
  /// Prints a counterexample vmt-style.
  pub fn print_vmt(
    & self, props: & [ Sym ]
  ) {
    print!("(cex\n  ( ") ;
    for prop in props.iter() {
      print!("{} ", prop)
    }
    print!(")\n") ;

    // Printing function symbols.
    if self.no_state.is_empty() {
      print!("  () ; no function symbols\n")
    } else {
      print!("  ( ; function symbols:") ;
      for (ref sym, ref cst) in self.no_state.iter() {
        print!(
          "\n    (declare-fun {} () {} {})", sym, cst.typ(), cst
        )
      }
      print!("\n  )\n") ;
    }

    // Printing states.
    let mut off = Offset::zero() ;
    while let Some( ref cex ) = self.trace.get(& off) {
      print!("  ; state {}:\n  (and\n", off) ;
      for (ref sym, ref cst) in cex.iter() {
        print!("    (= {} {})\n", sym, cst)
      }
      print!("  )\n") ;
      off = off.nxt()
    }

    print!(")\n")
  }
  /// Formats a counterexample human-style.
  pub fn format(& self) -> String {
    use std::cmp::max ;
    // First, we format all constants as strings and compute the maximal width
    // necessary for each symbol. We also compute the maximum length of the
    // offsets as a string.
    let mut cst_lens = HashMap::new() ;
    let args = self.sys.state().args() ;
    for & (ref sym, _) in args {
      cst_lens.insert(
        sym.get().clone(), format!("{}", sym).len()
      ) ;
    } ;
    let sys_name = format!("{}", self.sys.sym()) ;
    let mut offset_len = sys_name.len() ;
    for (ref off, ref map) in self.trace.iter() {
      // Max offset length.
      offset_len = max(
        format!("{}",off).len(), offset_len
      ) ;
      for (ref sym, ref cst) in map.iter() {
        let len = format!("{}", cst).len() ;
        let len = match cst_lens.get(sym) {
          None => unreachable!(),
          Some(l) => max(* l, len),
        } ;
        cst_lens.insert((* sym).clone(), len) ;
        ()
      }
    }
    // Computing maximal non-stateful symbol max length.
    let mut no_state_len = 0 ;
    for (ref sym, _) in self.no_state.iter() {
      no_state_len = max(no_state_len, format!("{}", sym).len())
    } ;

    // Begin formatting.
    let mut s = String::new() ;

    // No-state values.
    if ! self.no_state.is_empty() {
      s = format!("declare-funs:") ;
      for (ref sym, ref cst) in self.no_state.iter() {
        s = format!("{}\n  {2:^1$} = {3}", s, no_state_len, sym, cst)
      } ;
      s = format!("{}\ntrace:\n", s)
    }

    // State values.
    let mut offset = Offset::zero() ;
    s = format!("{}  {}", s, sys_name) ;
    let mut sep = String::new() ;
    for _ in 0..(offset_len - sys_name.len()) {
      s.push(' ')
    } ;
    for _ in 0..offset_len {
      sep.push('-')
    } ;
    for & (ref sym, _) in args {
      s = format!("{} | ", s) ;
      sep = format!("{}-|-", sep) ;
      let fmt = format!("{}", sym) ;
      s = format!("{}{}", s, fmt) ;
      let width = cst_lens.get(sym).unwrap() ;
      if width > & fmt.len() {
        for _ in 0..(width - fmt.len()) {
          s.push(' ')
        } ;
      }
      for _ in 0..(* width) {
        sep.push('-')
      } ;
    } ;
    s = format!("{}\n  {}", s, sep) ;
    loop {
      match self.trace.get(& offset) {
        Some(map) => {
          s = format!("{}\n  ", s) ;
          let fmt = format!("{}", offset) ;
          if offset_len > fmt.len() {
            for _ in 0..(offset_len - fmt.len()) {
              s.push(' ')
            } ;
          }
          s = format!("{}{}", s, fmt) ;
          for & (ref sym, _) in args.iter() {
            s = format!("{} | ", s) ;
            let width = cst_lens.get(sym).unwrap() ;
            let fmt = match map.get(sym) {
              Some(ref cst) => format!("{}", cst),
              None => "-".to_string(),
            } ;
            if width > & fmt.len() {
              for _ in 0..(width - fmt.len()) {
                s.push(' ')
              } ;
            }
            s = format!("{}{}", s, fmt)
          }
        },
        None => break,
      } ;
      offset = offset.nxt()
    } ;
    s
  }
}

/// Maintains the context and can read commands from an `io::Read`.
/// 
/// Input is read line per line.
/// 
/// ## Checks
/// 
/// During parsing, checks the errors corresponding to [`Error`][error].
/// 
/// [error]: enum.Error.html (The Error enum)
pub struct Context {
  /// Number of lines **read** so far. Does not correspond to where the parser
  /// is currently at. Not really used at the moment.
  line: usize,
  /// String buffer for swapping when reading, and remember stuff when reading
  /// from stdin.
  buffer: String,
  /// Term factory.
  factory: Factory,
  /// All symbols defined. Used for faster redefinition checking.
  all: HashSet<Sym>,
  // /// State definitions.
  // states: HashMap<Sym, Arc<State>>,
  /// Function symbol declarations and definitions.
  callables: HashMap<Sym, ::Callable>,
  /// Map from systems to properties.
  props: HashMap<Sym, (::Prop, PropStatus)>,
  /// Systems.
  syss: HashMap<Sym, ::Sys>,
  /// Maps system identifiers to their invariants.
  invs: HashMap<Sym, STermSet>,
}
impl Context {
  /// Creates an empty context.
  /// 
  /// All tables in the context are created with a capacity that's a prime
  /// number. It's useless but looks pretty cool.
  pub fn mk(factory: Factory, buffer_size: usize) -> Self {
    Context {
      line: 0,
      buffer: String::with_capacity(buffer_size),
      factory: factory,
      all: HashSet::with_capacity(127),
      // states: HashMap::with_capacity(23),
      callables: HashMap::with_capacity(23),
      props: HashMap::with_capacity(53),
      // inits: HashMap::with_capacity(23),
      // transs: HashMap::with_capacity(23),
      syss: HashMap::with_capacity(23),
      invs: HashMap::with_capacity(127),
    }
  }

  // /// Option of the state corresponding to an identifier.
  // #[inline]
  // pub fn get_state(& self, sym: & Sym) -> Option<& ::State> {
  //   self.states.get(sym)
  // }
  /// Option of the function declaration/definition corresponding to an
  /// identifier.
  #[inline]
  pub fn get_callable(& self, sym: & Sym) -> Option<& ::Callable> {
    self.callables.get(sym)
  }
  /// Option of the property corresponding to an identifier.
  #[inline]
  pub fn get_prop(& self, sym: & Sym) -> Option<& (::Prop, PropStatus) > {
    self.props.get(sym)
  }
  /// Updates the status of a property to invariant.
  pub fn set_prop_k_true(
    & mut self, sym: & Sym, k: usize
  ) -> Result<(), String> {
    if let Some( & mut (_, ref mut status) ) = self.props.get_mut(sym) {
      match * status {
        PropStatus::Falsified(ref cex) => if k < cex.len() {
          return Ok(())
        } else {
          return Err(
            format!(
              "[Context::set_prop_inv] cannot set property {}-true\n\
              property's status is falsified at {}",
              k, cex.len()
            )
          )
        },
        PropStatus::KTrue(old_k) => if k <= old_k {
          return Ok(())
        },
        PropStatus::Invariant(_) => return Ok(()),
        _ => (),
      }
      * status = PropStatus::KTrue(k) ;
      Ok(())
    } else {
      Err(
        format!("[Context::set_prop_inv] unknown property {}", sym)
      )
    }
  }
  /// Updates the status of a property to invariant.
  pub fn set_prop_inv(& mut self, sym: & Sym, k: usize) -> Result<(), String> {
    if let Some( & mut (_, ref mut status) ) = self.props.get_mut(sym) {
      match * status {
        PropStatus::Falsified(ref cex) => return Err(
          format!(
            "[Context::set_prop_inv] cannot set property invariant at {}\n\
            property's status is falsified at {}",
            k, cex.len()
          )
        ),
        PropStatus::Invariant(old_k) => if old_k <= k {
          return Ok(())
        },
        _ => (),
      }
      * status = PropStatus::Invariant(k) ;
      Ok(())
    } else {
      Err(
        format!("[Context::set_prop_inv] unknown property {}", sym)
      )
    }
  }
  /// Updates the status of a property to falsified.
  pub fn set_prop_false(
    & mut self, sym: & Sym, cex: Cex
  ) -> Result<(), String> {
    if let Some( & mut (_, ref mut status) ) = self.props.get_mut(sym) {
      match * status {
        PropStatus::Invariant(k) => return Err(
          format!(
            "[Context::set_prop_false] cannot set property false at {}\n\
            property's status is proved at {}",
            cex.len(), k
          )
        ),
        PropStatus::KTrue(k) => if k >= cex.len() {
          return Err(
            format!(
              "[Context::set_prop_false] cannotset property false at {}\n\
              property's status is {}-true", cex.len(), k
            )
          )
        },
        _ => (),
      }
      * status = PropStatus::Falsified(cex) ;
      Ok(())
    } else {
      Err(
        format!("[Context::set_prop_false] unknown property {}", sym)
      )
    }
  }

  /// Returns true iff some properties are neither proved or disproved.
  #[inline]
  pub fn some_prop_unknown(& self, props: & [::Prop]) -> Result<bool, String> {
    for prop in props {
      match self.props.get( prop.sym() ) {
        Some( & (_, PropStatus::Unknown) ) => return Ok(true),
        Some( & (_, PropStatus::KTrue(_)) ) => return Ok(true),
        Some( _ ) => (),
        None => return Err(
          format!("[Context::any_prop_unknown] unknown property {}", prop)
        ),
      }
    }
    Ok(false)
  }

  /// Returns the unknown properties.
  #[inline]
  pub fn unknown_props<'a>(
    & self, props: & 'a [::Prop]
  ) -> Result<Vec<& 'a Sym>, String> {
    let mut res = vec![] ;
    for prop in props {
      match self.props.get( prop.sym() ) {
        Some( & (_, PropStatus::Unknown) ) => res.push(
          prop.sym().get()
        ),
        Some( & (_, PropStatus::KTrue(_)) ) => res.push(
          prop.sym().get()
        ),
        Some( _ ) => (),
        None => return Err(
          format!("[Context::unknown_props] unknown property {}", prop)
        ),
      }
    }
    Ok(res)
  }

  /// Returns true iff some properties are disproved.
  #[inline]
  pub fn some_prop_disproved(
    & self, props: & [::Prop]
  ) -> Result<bool, String> {
    for prop in props {
      match self.props.get( prop.sym() ) {
        Some( & (_, PropStatus::Falsified(_)) ) => return Ok(true),
        Some( _ ) => (),
        None => return Err(
          format!("[Context::any_prop_unknown] unknown property {}", prop)
        ),
      }
    }
    Ok(false)
  }

  /// Option of the system corresponding to an identifier.
  #[inline]
  pub fn get_sys(& self, sym: & Sym) -> Option<& ::Sys> {
    self.syss.get(sym)
  }

  /// Add invariants for a system.
  #[inline]
  pub fn add_invs(
    & mut self, sym: & Sym, invs: STermSet
  ) -> Result<(), String> {
    if let Some(set) = self.invs.get_mut(sym) {
      if set.is_empty() {
        * set = invs
      } else {
        use std::iter::Extend ;
        set.extend(invs)
      }
      return Ok(())
    }

    // Reacheable iff `self.invs` is not defined for `sym`.
    if self.syss.contains_key(sym) {
      self.invs.insert(sym.clone(), invs) ;
      Ok(())
    } else {
      Err(
        format!("[Context::add_invs] unknown system {}", sym)
      )
    }
  }

  /// Prints the state of the context to stdin. Used for debugging. See also
  /// [the `lines` function][lines fun].
  ///
  /// [lines fun]: struct.Context.html#method.lines (The lines function)
  pub fn stdin_print(& self) {
    println!("Context:") ;
    for line in self.lines().lines() {
      println!("  {}", line)
    }
  }

  /// Option of the item corresponding to an identifier.
  pub fn sym_unused(& self, sym: & Sym) -> Option<& 'static str> {
    use base::Callable::* ;
    if ! self.all.contains(sym) { None } else {
      // try_get!(self.states, sym, state_desc) ;
      try_get!(
        self.callables, sym, callable => {
          match * * callable {
            Dec(_) => uf_desc,
            Def(_) => fun_desc,
          }
        }
      ) ;
      try_get!(self.props, sym, prop_desc) ;
      // try_get!(self.inits, sym, init_desc) ;
      // try_get!(self.transs, sym, trans_desc) ;
      try_get!(self.syss, sym, sys_desc) ;
      self.stdin_print() ;
      println!("") ;
      println!("error, sym \"{}\" is in `all` but in none of the maps", sym) ;
      unreachable!() ;
    }
  }

  /// A multiline string representation of the state of a context.
  pub fn lines(& self) -> String {
    let mut s = format!("line: {}\nbuffer: {}", self.line, self.buffer) ;
    s = map_to_lines(& self.callables, "function symbols:", s) ;
    s = format!("{}\nsystems: {{", s) ;
    for (_, ref sys) in self.syss.iter() {
      for line in sys.lines().lines() {
        s = format!("{}\n  {}", s, line)
      }
    } ;
    if ! self.syss.is_empty() { s = format!("{}\n}}", s) } ;
    map_pairs_to_lines(& self.props, "properties:", s)
  }

  /// Underlying symbol, constant and term factory.
  #[inline]
  pub fn factory(& self) -> & Factory { & self.factory }

  /// Reads lines and parses them until it finds
  ///
  /// * a check command,
  /// * an exit command, or
  /// * an error.
  pub fn read(
    & mut self, reader: & mut io::Read
  ) -> Result<Res, Error> {
    use nom::IResult::* ;
    use std::io::{ BufRead, BufReader } ;
    use std::str ;
    let mut lines = BufReader::new(reader).lines() ;
    let mut buffer = String::with_capacity(self.buffer.capacity()) ;
    // panic!("bla")
    loop {
      let mut new_things = false ;

      // println!("  entering lines loop") ;
      loop {
        match lines.next() {
          Some(Ok(line)) => {
            self.line = self.line + 1 ;
            match comment(line.as_bytes()) {
              Done(chars, _) => {
                // Comment necessarily parses the whole line.
                assert!( chars.len() == 0 ) ;
                ()
              },
              Incomplete(_) => {
                // Can be incomplete if line is empty.
                assert!( line.trim().len() == 0 ) ;
                ()
              },
              _ => {
                // Not a line containing only comments.
                self.buffer.push('\n') ;
                self.buffer.push_str(& line) ;
                new_things = true
              },
            }
          },
          Some(Err(e)) => return Err( check::Error::Io(e) ),
          None => {
            if new_things { break } else {
              sleep(Duration::from_millis(10))
            }
          }
        }
      }

      // println!("  entering parse loop") ;
      loop {
        // println!("  updating") ;
        buffer.clear() ;
        buffer.push_str(& self.buffer) ;
        // println!(
        //   "  buffer capacity: {}, {}",
        //   buffer.capacity(), self.buffer.capacity()
        // ) ;
        // println!("  buffers: {}", buffer) ;
        // println!("         : {}", self.buffer) ;
        match item_parser(buffer.as_bytes(), self) {
          Done(chars, Ok(())) => {
            self.buffer.clear() ;
            self.buffer.push_str(str::from_utf8(chars).unwrap()) ;
          },
          Done(_, Err(e)) => return Err(e),
          Incomplete(_) => {
            println!("Context:") ;
            for line in self.lines().lines() {
              println!("| {}", line)
            } ;
            println!("  incomplete (item)") ;
            break
          },
          _ => match check_exit_parser(buffer.as_bytes(), self) {
            Done(chars, res) => {
              self.buffer.clear() ;
              self.buffer.push_str(str::from_utf8(chars).unwrap()) ;
              return res.map(|res| res.destroy().0)
            },
            Incomplete(_) => {
              println!("Context:") ;
              for line in self.lines().lines() {
                println!("| {}", line)
              } ;
              println!("  incomplete (check)") ;
              break
            },
            _ => {
              println!("Context:") ;
              for line in self.lines().lines() {
                println!("| {}", line)
              } ;
              panic!("what's that: {}", buffer)
            },
          }
        }
      }
    }
  }

  /// Returns a counterexample for a system from a model.
  ///
  /// Assumes the offset **does not have reverse semantics**. That is, the
  /// model does not come from a backward unrolling.
  pub fn cex_of(& self, model: & Model, sys: & ::Sys) -> Cex {
    let mut no_state = HashMap::new() ;
    let mut trace = HashMap::<Offset, HashMap<Sym, Cst>>::new() ;
    let state = sys.state() ;
    for & ( ref pair, ref cst ) in model.iter() {
      let (ref var, ref off_opt) = * pair ;
      match * off_opt {
        None => match self.sym_unused(var.sym()) {
          Some(_) => {
            let old = no_state.insert(var.get().sym().clone(), cst.clone()) ;
            if let Some(old) = old {
              panic!(
                "var {} appears twice ({}, {}) in model for {}",
                var, old, cst, sys.sym()
              )
            }
          },
          None => (),
        },
        Some(ref off) => if state.contains(var.get().sym()) {
          let map = match trace.get_mut(off) {
            Some(ref mut map) => {
              map.insert(var.get().sym().clone(), cst.clone()) ;
              continue
            },
            None => {
              let mut map = HashMap::with_capacity(state.len()) ;
              map.insert(var.get().sym().clone(), cst.clone()) ;
              map
            },
          } ;
          trace.insert(off.clone(), map) ; ()
        } else {
          panic!(
            "state var {} is not in the state of system {}", var, sys.sym()
          )
        },
      }
    }

    Cex { sys: sys.clone(), no_state: no_state, trace: trace }
  }


  fn internal_add_callable(& mut self, fun: Callable) {
    let sym = fun.sym().clone() ;
    match self.all.insert(sym.clone()) {
      true => (),
      false => panic!(
        println!("added callable {} but symbol is already used", sym)
      ),
    }
    match self.callables.insert(sym, Arc::new(fun)) {
      None => (),
      Some(e) => {
        self.stdin_print() ;
        println!("added {} which already exists in callables", e) ;
        unreachable!()
      },
    }
  }
  fn internal_add_prop(& mut self, prop: Prop, status: PropStatus) {
    let sym = prop.sym().get().clone() ;
    match self.all.insert(sym.clone()) {
      true => (),
      false => panic!(
        println!("added prop {} but symbol is already used", sym)
      ),
    }
    match self.props.insert(sym, (Arc::new(prop), status)) {
      None => (),
      Some(e) => {
        self.stdin_print() ;
        println!("added {} which already exists in props ({})", e.0, e.1) ;
        unreachable!()
      },
    }
  }
  fn internal_add_sys(& mut self, sys: Sys) {
    let sym = sys.sym().clone() ;
    match self.all.insert(sym.clone()) {
      true => (),
      false => panic!(
        println!("added system {} but symbol is already used", sym)
      ),
    }
    match self.syss.insert(sym, Arc::new(sys)) {
      None => (),
      Some(e) => {
        self.stdin_print() ;
        println!("added {} which already exists in syss", e) ;
        unreachable!()
      },
    }
  }


  /// Adds a function declaration to the context.
  pub fn add_fun_dec(
    & mut self, sym: Spnd<Sym>, sig: Sig, typ: Spnd<Type>
  ) -> Result<(), Error> {
    match check::check_fun_dec(self, sym, sig, typ) {
      Ok(callable) => Ok( self.internal_add_callable(callable) ),
      Err(e) => Err(e),
    }
  }

  /// Adds a function definition to the context.
  pub fn add_fun_def(
    & mut self, sym: Spnd<Sym>, args: Args, typ: Spnd<Type>, body: TermAndDep
  ) -> Result<(), Error> {
    match check::check_fun_def(self, sym, args, typ, body) {
      Ok(callable) => Ok( self.internal_add_callable(callable) ),
      Err(e) => Err(e),
    }
  }

  /// Adds a state property definition to the context.
  pub fn add_prop(
    & mut self, sym: Spnd<Sym>, sys: Spnd<Sym>, body: TermAndDep
  ) -> Result<(), Error> {
    match check::check_prop(self, sym, sys, body) {
      Ok(prop) => Ok( self.internal_add_prop(prop, PropStatus::Unknown) ),
      Err(e) => Err(e),
    }
  }

  /// Adds a state relation definition to the context.
  pub fn add_rel(
    & mut self, sym: Spnd<Sym>, sys: Spnd<Sym>, body: TermAndDep
  ) -> Result<(), Error> {
    match check::check_rel(self, sym, sys, body) {
      Ok(rel) => Ok( self.internal_add_prop(rel, PropStatus::Unknown) ),
      Err(e) => Err(e),
    }
  }

  /// Adds a system definition to the context.
  pub fn add_sys(
    & mut self, sym: Sym, state: Args,
    locals: Vec<(Sym, Type, TermAndDep)>,
    init: TermAndDep, trans: TermAndDep,
    sub_syss: Vec<(Spnd<Sym>, Vec<TermAndDep>)>
  ) -> Result<(), Error> {
    match check::check_sys(
      self, sym, state, locals, init, trans, sub_syss
    ) {
      Ok(sys) => Ok( self.internal_add_sys(sys) ),
      Err(e) => Err(e),
    }
  }

}