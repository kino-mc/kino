// Copyright 2015 Adrien Champion. See the COPYRIGHT file at the top-level
// directory of this distribution.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

/*! System parsing. */

use std::thread::sleep_ms ;
use std::collections::{ HashSet, HashMap } ;
use std::fmt ;
use std::io ;

use term::{ Sym, Factory } ;

use base::* ;

mod parsers ;
mod check ;
pub use self::check::Error ;

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
    acc = format!("{}\n}}", acc)
  } else {
    acc = format!("{}}}", acc)
  } ;
  acc
}

macro_rules! try_get {
  ($map:expr, $sym:expr, $id:ident => $b:block) => (
    match $map.get($sym) {
      None => (),
      Some($id) => return Some($b),
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

/** Maintains the parsing context and parses commands from a `io::Read`.

During parsing, checks the errors corresponding to `Error`.
That is, checks that none of the following happens

| *description*                                     | `Error` variant |
|:--------------------------------------------------|:----------------|
| redefinition of identifier                        | `Redef`         |
| state variables in `define-fun`s                  | `SVarInDef`     |
| application of unknown function symbol            | `UkCall`        |
| unknown state identifier                          | `UkState`       |
| unknown (state) variable *w.r.t.* current state   | `UkVar`         |
| unknown init identifier in system                 | `UkInit`        |
| unknown trans identifier in system                | `UkTrans`       |
| inconsistent state between systems and init/trans | `IncState`      |
| unknown system identifier in check                | `UkSys`         |
| unknown pred identifier in check                  | `UkPred`        |
| inconsistent state of preds in check              | `IncPredState`  |
| state variable used in next state in init         | `NxtInit`       |


**Does not** do

* function symbol application arity checking
* type checking

*/
pub struct Context {
  /** Number of lines **read** so far. Does not correspond to where the parser
  is currently at. */
  line: usize,
  /** String buffer for swapping when reading, and remember stuff when reading
  from stdin. */
  buffer: String,
  /** Term factory. */
  factory: Factory,
  /** All symbols defined. Used for faster redefinition checking. */
  all: HashSet<Sym>,
  /** State definitions. */
  states: HashMap<Sym, State>,
  /** Function symbol declarations and definitions. */
  callables: HashMap<Sym, Callable>,
  /** Prediacte definitions. */
  preds: HashMap<Sym, Pred>,
  /** Init predicate definitions. */
  inits: HashMap<Sym, Init>,
  /** Transition predicate definitions. */
  transs: HashMap<Sym, Trans>,
  /** Systems. */
  syss: HashMap<Sym, Sys>,
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
      states: HashMap::with_capacity(23),
      callables: HashMap::with_capacity(23),
      preds: HashMap::with_capacity(53),
      inits: HashMap::with_capacity(23),
      transs: HashMap::with_capacity(23),
      syss: HashMap::with_capacity(23),
    }
  }

  /** Option of the state corresponding to an identifier. */
  #[inline(always)]
  pub fn get_state(& self, sym: & Sym) -> Option<& State> {
    self.states.get(sym)
  }
  /** Option of the function declaration/definition corresponding to an
  identifier. */
  #[inline(always)]
  pub fn get_callable(& self, sym: & Sym) -> Option<& Callable> {
    self.callables.get(sym)
  }
  /** Option of the predicate corresponding to an identifier. */
  #[inline(always)]
  pub fn get_pred(& self, sym: & Sym) -> Option<& Pred> {
    self.preds.get(sym)
  }
  /** Option of the init corresponding to an identifier. */
  #[inline(always)]
  pub fn get_init(& self, sym: & Sym) -> Option<& Init> {
    self.inits.get(sym)
  }
  /** Option of the trans corresponding to an identifier. */
  #[inline(always)]
  pub fn get_trans(& self, sym: & Sym) -> Option<& Trans> {
    self.transs.get(sym)
  }
  /** Option of the system corresponding to an identifier. */
  #[inline(always)]
  pub fn get_sys(& self, sym: & Sym) -> Option<& Sys> {
    self.syss.get(sym)
  }

  /** Prints the state of the context to stdin. Used for debugging. See also
  `lines(& self)`. */
  pub fn stdin_print(& self) {
    println!("Context:") ;
    for line in self.lines().lines() {
      println!("| {}", line)
    }
  }

  /** Option of the item corresponding to an identifier. */
  pub fn item_of_sym(& self, sym: & Sym) -> Option<Item> {
    use base::Item::* ;
    use base::Callable::* ;
    if ! self.all.contains(sym) { None } else {
      try_get!(
        self.states, sym, state => { St(state.clone()) }
      ) ;
      try_get!(
        self.callables, sym, callable => {
          match * callable {
            Dec(ref f) => FDc(f.clone()),
            Def(ref f) => FDf(f.clone()),
          }
        }
      ) ;
      try_get!(
        self.preds, sym, pred => { P(pred.clone()) }
      ) ;
      try_get!(
        self.inits, sym, init => { I(init.clone()) }
      ) ;
      try_get!(
        self.transs, sym, trans => { T(trans.clone()) }
      ) ;
      try_get!(
        self.syss, sym, sys => { S(sys.clone()) }
      ) ;
      self.stdin_print() ;
      println!("") ;
      println!("error, sym \"{}\" is in `all` but in none of the maps", sym) ;
      unreachable!() ;
    }
  }

  /** Checks the item is legal and adds it where it belongs if it is. */
  pub fn add(& mut self, i: Item) -> Result<(), Error> {
    use base::Item::* ;
    use base::Callable::* ;
    try!( check::check_item(& self, & i) ) ;
    let sym = i.sym().clone() ;
    match i {
      St(state) => {
        match self.states.insert(sym, state) {
          None => (),
          Some(e) => {
            self.stdin_print() ;
            println!("added {} which already exists in states", e.sym()) ;
            unreachable!()
          }
        }
      },
      FDc(f) => {
        match self.callables.insert(sym, Dec(f)) {
          None => (),
          Some(e) => {
            self.stdin_print() ;
            println!("added {} which already exists in callables", e.sym()) ;
            unreachable!()
          }
        }
      },
      FDf(f) => {
        match self.callables.insert(sym, Def(f)) {
          None => (),
          Some(e) => {
            self.stdin_print() ;
            println!("added {} which already exists in callables", e.sym()) ;
            unreachable!()
          }
        }
      },
      P(pred) => {
        match self.preds.insert(sym, pred) {
          None => (),
          Some(e) => {
            self.stdin_print() ;
            println!("added {} which already exists in preds", e.sym()) ;
            unreachable!()
          }
        }
      },
      I(init) => {
        match self.inits.insert(sym, init) {
          None => (),
          Some(e) => {
            self.stdin_print() ;
            println!("added {} which already exists in inits", e.sym()) ;
            unreachable!()
          }
        }
      },
      T(trans) => {
        match self.transs.insert(sym, trans) {
          None => (),
          Some(e) => {
            self.stdin_print() ;
            println!("added {} which already exists in transs", e.sym()) ;
            unreachable!()
          }
        }
      },
      S(sys) => {
        match self.syss.insert(sym, sys) {
          None => (),
          Some(e) => {
            self.stdin_print() ;
            println!("added {} which already exists in syss", e.sym()) ;
            unreachable!()
          }
        }
      },
    }
    Ok(())
  }

  /** A multiline string representation of the state of a context. */
  pub fn lines(& self) -> String {
    let s = format!("line: {}\nbuffer: {}", self.line, self.buffer) ;
    let s = map_to_lines(& self.callables, "function symbols:", s) ;
    let s = map_to_lines(& self.states, "states:", s) ;
    let s = map_to_lines(& self.preds, "preds:", s) ;
    let s = map_to_lines(& self.inits, "inits:", s) ;
    let s = map_to_lines(& self.transs, "transs:", s) ;
    let s = map_to_lines(& self.syss, "syss:", s) ;
    s
  }

  /** Underlying buffer as bytes. */
  pub fn bytes(& self) -> & [u8] { self.buffer.as_bytes() }

  /** Underlying term factory. */
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
}
