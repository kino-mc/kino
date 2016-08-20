// Copyright 2015 Adrien Champion. See the COPYRIGHT file at the top-level
// directory of this distribution.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

/*! System parsing.

## To do

Context:

* hash of `Item` should be hash of its `Sym`, and replace hash maps with hash
  sets
*/

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
  TermAndDep, Type, Offset, Cst, Sym, Term, Factory, Model
} ;

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

/** A positive or negative literal. */
pub enum Atom {
  /** A positive literal. */
  Pos(Sym),
  /** A negative literal. */
  Neg(Sym),
}
impl Atom {
  #[inline]
  pub fn sym(& self) -> & Sym {
    match * self {
      Atom::Pos(ref sym) => sym,
      Atom::Neg(ref sym) => sym,
    }
  }
  #[inline]
  pub fn into_var(self, f: & Factory) -> Term {
    use term::VarMaker ;
    match self {
      Atom::Pos(sym) => f.var(sym),
      Atom::Neg(sym) => f.not( f.var(sym) ),
    }
  }
}

/** Normal result of a parsing attempt. */
#[derive(Debug)]
pub enum Res {
  /** Found an exit command. */
  Exit,
  /** Found a check command. */
  Check(::Sys, Vec<::Prop>),
  /** Found a check with assumptions command. */
  CheckAss(::Sys, Vec<::Prop>, Vec<Term>)
}
impl Res {
  /** A multi-line representation of the result of a parsing attempty */
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

/** A counterexample for a system. */
pub struct Cex {
  sys: ::Sys,
  no_state: HashMap<Sym, Cst>,
  trace: HashMap<Offset, HashMap<Sym, Cst>>
}
impl Cex {
  /** Length of a cex. Number of states minus one. */
  pub fn len(& self) -> usize {
    assert!(self.trace.len() > 0) ;
    self.trace.len() - 1
  }
  /** Formats a counterexample. */
  pub fn format(& self) -> String {
    use std::cmp::max ;
    // First, we format all constants as strings and compute the maximal width
    // necessary for each symbol. We also compute the maximum length of the
    // offsets as a string.
    let mut cst_lens = HashMap::new() ;
    let args = self.sys.state().args() ;
    for & (ref sym, _) in args {
      cst_lens.insert(
        sym.clone(), format!("{}", sym).len()
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

/** Maintains the context and can read commands from an `io::Read`.

Input is read line per line.

## Does **not** check

* function symbol application arity checking
* type checking

These will be done elsewhere for efficiency.

## Checks

During parsing, checks the errors corresponding to [`Error`][error].

[error]: enum.Error.html (The Error enum)
*/
pub struct Context {
  /** Number of lines **read** so far. Does not correspond to where the parser
  is currently at. Not really used at the moment. */
  line: usize,
  /** String buffer for swapping when reading, and remember stuff when reading
  from stdin. */
  buffer: String,
  /** Term factory. */
  factory: Factory,
  /** All symbols defined. Used for faster redefinition checking. */
  all: HashSet<Sym>,
  // /** State definitions. */
  // states: HashMap<Sym, Arc<State>>,
  /** Function symbol declarations and definitions. */
  callables: HashMap<Sym, ::Callable>,
  /** Propiacte definitions. */
  props: HashMap<Sym, ::Prop>,
  // /** Init property definitions. */
  // inits: HashMap<Sym, Arc<Init>>,
  // /** Transition property definitions. */
  // transs: HashMap<Sym, Arc<Trans>>,
  /** Systems. */
  syss: HashMap<Sym, ::Sys>,
  // /** Maps system identifiers to their invariants. */
  // invs: HashMap<Sym, HashSet<Prop>>,
}
impl Context {
  /** Creates an empty context.

  All tables in the context are created with capacity that's a prime number.
  It's useless but looks pretty cool.
  */
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
      // invs: HashMap::with_capacity(127),
    }
  }

  // /** Option of the state corresponding to an identifier. */
  // #[inline(always)]
  // pub fn get_state(& self, sym: & Sym) -> Option<& ::State> {
  //   self.states.get(sym)
  // }
  /** Option of the function declaration/definition corresponding to an
  identifier. */
  #[inline(always)]
  pub fn get_callable(& self, sym: & Sym) -> Option<& ::Callable> {
    self.callables.get(sym)
  }
  /** Option of the property corresponding to an identifier. */
  #[inline(always)]
  pub fn get_prop(& self, sym: & Sym) -> Option<& ::Prop> {
    self.props.get(sym)
  }
  /** Option of the system corresponding to an identifier. */
  #[inline(always)]
  pub fn get_sys(& self, sym: & Sym) -> Option<& ::Sys> {
    self.syss.get(sym)
  }

  /** Prints the state of the context to stdin. Used for debugging. See also
  [the `lines` function][lines fun].

  [lines fun]: struct.Context.html#method.lines (The lines function) */
  pub fn stdin_print(& self) {
    println!("Context:") ;
    for line in self.lines().lines() {
      println!("  {}", line)
    }
  }

  /** Option of the item corresponding to an identifier. */
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

  /** A multiline string representation of the state of a context. */
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
    map_to_lines(& self.props, "properties:", s)
  }

  /** Underlying symbol, constant and term factory. */
  #[inline(always)]
  pub fn factory(& self) -> & Factory { & self.factory }

  /** Reads lines and parses them until it finds

  * a check command,
  * an exit command, or
  * an error. */
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
                assert!( line.len() == 0 ) ;
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
              return res
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

  /** Returns a counterexample for a system from a model.

  Assumes the offset **does not have reverse semantics**. That is, the model
  does not come from a backward unrolling.*/
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
  fn internal_add_prop(& mut self, prop: Prop) {
    let sym = prop.sym().clone() ;
    match self.all.insert(sym.clone()) {
      true => (),
      false => panic!(
        println!("added prop {} but symbol is already used", sym)
      ),
    }
    match self.props.insert(sym, Arc::new(prop)) {
      None => (),
      Some(e) => {
        self.stdin_print() ;
        println!("added {} which already exists in props", e) ;
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


  /** Adds a function declaration to the context. */
  pub fn add_fun_dec(
    & mut self, sym: Sym, sig: Sig, typ: Type
  ) -> Result<(), Error> {
    match check::check_fun_dec(self, sym, sig, typ) {
      Ok(callable) => Ok( self.internal_add_callable(callable) ),
      Err(e) => Err(e),
    }
  }

  /** Adds a function definition to the context. */
  pub fn add_fun_def(
    & mut self, sym: Sym, args: Args, typ: Type, body: TermAndDep
  ) -> Result<(), Error> {
    match check::check_fun_def(self, sym, args, typ, body) {
      Ok(callable) => Ok( self.internal_add_callable(callable) ),
      Err(e) => Err(e),
    }
  }

  /** Adds a state property definition to the context. */
  pub fn add_prop(
    & mut self, sym: Sym, sys: Sym, body: TermAndDep
  ) -> Result<(), Error> {
    match check::check_prop(self, sym, sys, body) {
      Ok(prop) => Ok( self.internal_add_prop(prop) ),
      Err(e) => Err(e),
    }
  }

  /** Adds a state relation definition to the context. */
  pub fn add_rel(
    & mut self, sym: Sym, sys: Sym, body: TermAndDep
  ) -> Result<(), Error> {
    match check::check_rel(self, sym, sys, body) {
      Ok(rel) => Ok( self.internal_add_prop(rel) ),
      Err(e) => Err(e),
    }
  }

  /** Adds a system definition to the context. */
  pub fn add_sys(
    & mut self, sym: Sym, state: Args,
    locals: Vec<(Sym, Type, TermAndDep)>,
    init: TermAndDep, trans: TermAndDep,
    sub_syss: Vec<(Sym, Vec<TermAndDep>)>
  ) -> Result<(), Error> {
    match check::check_sys(
      self, sym, state, locals, init, trans, sub_syss
    ) {
      Ok(sys) => Ok( self.internal_add_sys(sys) ),
      Err(e) => Err(e),
    }
  }

}