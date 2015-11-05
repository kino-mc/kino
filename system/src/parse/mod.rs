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

static uf_desc:    & 'static str = "function declaration" ;
static fun_desc:   & 'static str = "function definition"  ;
static prop_desc:  & 'static str = "property definition"  ;
static sys_desc:   & 'static str = "system definition"    ;

use std::io ;
use std::fmt ;
use std::rc::Rc ;
use std::thread::sleep_ms ;
use std::collections::{ HashSet, HashMap } ;

use term::{ Sym, Factory } ;

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

/** Normal result of a parsing attempt. */
pub enum Res {
  /** Found an exit command. */
  Exit,
  /** Found a check command. */
  Check(Sym, Vec<Sym>),
}

/** Maintains the context and can read commands from an `io::Read`.

Input is read line per line.

## Does **not** check

* function symbol application arity checking
* type checking

These will be done elsewhere for efficiency.

## Checks

During parsing, checks the errors corresponding to [`Error`][error].
That is, checks that none of the following happens

| *description*                                   | `Error` variant |
|:------------------------------------------------|:----------------|
| redefinition of identifier                      | `Redef`         |
| state variables in a `define-fun`               | `SVarInDef`     |
| application of unknown function symbol          | `UkCall`        |
| unknown state identifier                        | `UkState`       |
| unknown (state) variable *w.r.t.* current state | `UkVar`         |
| unknown init identifier in system               | `UkInit`        |
| unknown trans identifier in system              | `UkTrans`       |
| inconsistent state between systems and init     | `IncInitState`  |
| inconsistent state between systems and trans    | `IncTransState` |
| unknown system identifier in check              | `UkSys`         |
| unknown prop identifier in check                | `UkProp`        |
| inconsistent state of props in check            | `IncPropState`  |
| state variable used in next state in init       | `NxtInit`       |

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
  // states: HashMap<Sym, Rc<State>>,
  /** Function symbol declarations and definitions. */
  callables: HashMap<Sym, Rc<Callable>>,
  /** Propiacte definitions. */
  props: HashMap<Sym, Rc<Prop>>,
  // /** Init property definitions. */
  // inits: HashMap<Sym, Rc<Init>>,
  // /** Transition property definitions. */
  // transs: HashMap<Sym, Rc<Trans>>,
  /** Systems. */
  syss: HashMap<Sym, Rc<Sys>>,
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
    }
  }

  // /** Option of the state corresponding to an identifier. */
  // #[inline(always)]
  // pub fn get_state(& self, sym: & Sym) -> Option<& Rc<State>> {
  //   self.states.get(sym)
  // }
  /** Option of the function declaration/definition corresponding to an
  identifier. */
  #[inline(always)]
  pub fn get_callable(& self, sym: & Sym) -> Option<& Rc<Callable>> {
    self.callables.get(sym)
  }
  /** Option of the property corresponding to an identifier. */
  #[inline(always)]
  pub fn get_prop(& self, sym: & Sym) -> Option<& Rc<Prop>> {
    self.props.get(sym)
  }
  // /** Option of the init corresponding to an identifier. */
  // #[inline(always)]
  // pub fn get_init(& self, sym: & Sym) -> Option<& Rc<Init>> {
  //   self.inits.get(sym)
  // }
  // /** Option of the trans corresponding to an identifier. */
  // #[inline(always)]
  // pub fn get_trans(& self, sym: & Sym) -> Option<& Rc<Trans>> {
  //   self.transs.get(sym)
  // }
  /** Option of the system corresponding to an identifier. */
  #[inline(always)]
  pub fn get_sys(& self, sym: & Sym) -> Option<& Rc<Sys>> {
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
          Some(Err(e)) => return Err( Error::Io(e) ),
          None => {
            if new_things { break } else {
              sleep_ms(10u32)
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
            // println!("  incomplete (item)") ;
            break
          },
          _ => match check_parser(buffer.as_bytes(), & self.factory) {
            Done(chars, check) => {
              self.buffer.clear() ;
              self.buffer.push_str(str::from_utf8(chars).unwrap()) ;
              try!( check::check_check(& self, & check) ) ;
              return Ok( Res::Check(check.0, check.1) )
            },
            Incomplete(_) => {
              println!("  incomplete (check)") ;
              break
            },
            _ => match exit_parser(buffer.as_bytes()) {
              Done(_,_) => return Ok(Res::Exit),
              Incomplete(_) => {
                // println!("  incomplete (exit)") ;
                ()
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
  }



  // fn build_sys(ctxt: & self, sym: Sym) -> super::sys::Sys {
  //   let mut ufs = vec![] ;
  //   let mut sub_sys = HashMap::new() ;
  //   let mut funs = vec![] ;

  //   // The unwraps below cannot fail, this comes after dependency checking. */

  //   let top = self.get(& sym).unwrap() ;
  //   let state = top.state().clone() ;
  //   let init = self.get(top.init()).unwrap() ;
  //   let trans = self.get(top.trans()).unwrap() ;
  // }
}



pub trait CanAdd {
  fn add_callable(& mut self, Callable) ;
  fn add_prop(& mut self, Prop) ;
  fn add_sys(& mut self, Sys) ;
}


impl CanAdd for Context {
  fn add_callable(& mut self, fun: Callable) {
    let sym = fun.sym().clone() ;
    match self.callables.insert(sym, Rc::new(fun)) {
      None => (),
      Some(e) => {
        self.stdin_print() ;
        println!("added {} which already exists in callables", e) ;
        unreachable!()
      },
    }
  }
  fn add_prop(& mut self, prop: Prop) {
    let sym = prop.sym().clone() ;
    match self.props.insert(sym, Rc::new(prop)) {
      None => (),
      Some(e) => {
        self.stdin_print() ;
        println!("added {} which already exists in props", e) ;
        unreachable!()
      },
    }
  }
  fn add_sys(& mut self, sys: Sys) {
    let sym = sys.sym().clone() ;
    match self.syss.insert(sym, Rc::new(sys)) {
      None => (),
      Some(e) => {
        self.stdin_print() ;
        println!("added {} which already exists in syss", e) ;
        unreachable!()
      },
    }
  }
}