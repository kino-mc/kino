// Copyright 2015 Adrien Champion. See the COPYRIGHT file at the top-level
// directory of this distribution.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use std::io ;
use std::fmt ;
use std::thread::sleep_ms ;
use std::collections::{ HashSet, HashMap } ;

use term::{ Sym, Type, Term, Factory } ;

#[derive(Debug,Clone)]
pub struct Sig {
  types: Vec<Type>,
}
impl Sig {
  #[inline(always)]
  pub fn mk(types: Vec<Type>) -> Self {
    Sig { types: types }
  }
  #[inline(always)]
  pub fn types(& self) -> & [Type] { & self.types }
}
impl fmt::Display for Sig {
  fn fmt(& self, fmt: & mut fmt::Formatter) -> fmt::Result {
    try!( write!(fmt, "(") ) ;
    let mut iter = self.types.iter() ;
    if let Some(ref t) = iter.next() {
      try!( write!(fmt, "{}", t) ) ;
      for t in iter {
        try!( write!(fmt, " {}", t) )
      }
    } ;
    write!(fmt, ")")
  }
}

#[derive(Debug,Clone)]
pub struct Args {
  args: Vec<(Sym, Type)>,
}
impl Args {
  #[inline(always)]
  pub fn mk(args: Vec<(Sym, Type)>) -> Self {
    Args { args: args }
  }
  #[inline(always)]
  pub fn args(& self) -> & [(Sym, Type)] { & self.args }
}
impl fmt::Display for Args {
  fn fmt(& self, fmt: & mut fmt::Formatter) -> fmt::Result {
    try!( write!(fmt, "(") ) ;
    let mut iter = self.args.iter() ;
    if let Some( & (ref s, ref t) ) = iter.next() {
      try!( write!(fmt, "({} {})", s, t) ) ;
      for & ( ref s, ref t) in iter {
        try!( write!(fmt, " ({} {})", s, t) )
      }
    } ;
    write!(fmt, ")")
  }
}

#[derive(Debug,Clone)]
pub struct State {
  sym: Sym,
  args: Args,
}
impl State {
  #[inline(always)]
  pub fn mk(sym: Sym, args: Args) -> Self {
    State { sym: sym, args: args }
  }
  #[inline(always)]
  pub fn sym(& self) -> & Sym { & self.sym }
  #[inline(always)]
  pub fn args(& self) -> & [(Sym, Type)] { self.args.args() }
}
impl fmt::Display for State {
  fn fmt(& self, fmt: & mut fmt::Formatter) -> fmt::Result {
    write!(fmt, "{}: {}", self.sym, self.args)
  }
}

#[derive(Debug,Clone)]
pub struct FunDec {
  sym: Sym,
  sig: Sig,
  typ: Type,
}
impl FunDec {
  #[inline(always)]
  pub fn mk(sym: Sym, sig: Sig, typ: Type) -> Self {
    FunDec { sym: sym, sig: sig, typ: typ }
  }
  #[inline(always)]
  pub fn sym(& self) -> & Sym { & self.sym }
  #[inline(always)]
  pub fn sig(& self) -> & [Type] { & self.sig.types() }
  #[inline(always)]
  pub fn typ(& self) -> & Type { & self.typ }
}
impl fmt::Display for FunDec {
  fn fmt(& self, fmt: & mut fmt::Formatter) -> fmt::Result {
    write!(fmt, "{}{} -> {}", self.sym, self.sig, self.typ)
  }
}

#[derive(Debug,Clone)]
pub struct Body {
  body: Term,
  calls: Vec<Sym>,
}
impl Body {
  /** Add calls in constructor late. */
  #[inline(always)]
  pub fn mk(body: Term) -> Self {
    Body { body: body, calls: vec![] }
  }
  #[inline(always)]
  pub fn body(& self) -> & Term { & self.body }
  #[inline(always)]
  pub fn calls(& self) -> & [Sym] { & self.calls }
}
impl fmt::Display for Body {
  fn fmt(& self, fmt: & mut fmt::Formatter) -> fmt::Result {
    write!(fmt, "{}", self.body)
  }
}

#[derive(Debug,Clone)]
pub struct FunDef {
  sym: Sym,
  args: Args,
  typ: Type,
  body: Body,
}
impl FunDef {
  #[inline(always)]
  pub fn mk(sym: Sym, args: Args, typ: Type, body: Body) -> Self {
    FunDef { sym: sym, args: args, typ: typ, body: body }
  }
  #[inline(always)]
  pub fn sym(& self) -> & Sym { & self.sym }
  #[inline(always)]
  pub fn args(& self) -> & [(Sym, Type)] { & self.args.args() }
  #[inline(always)]
  pub fn typ(& self) -> & Type { & self.typ }
  #[inline(always)]
  pub fn body(& self) -> & Body { & self.body }
}
impl fmt::Display for FunDef {
  fn fmt(& self, fmt: & mut fmt::Formatter) -> fmt::Result {
    write!(
      fmt, "{}{} -> {} {{ {} }}", self.sym, self.args, self.typ, self.body
    )
  }
}

#[derive(Debug,Clone)]
pub struct Pred {
  sym: Sym,
  state: Sym,
  body: Body,
}
impl Pred {
  #[inline(always)]
  pub fn mk(sym: Sym, state: Sym, body: Body) -> Self {
    Pred { sym: sym, state: state, body: body }
  }
  #[inline(always)]
  pub fn sym(& self) -> & Sym { & self.sym }
  #[inline(always)]
  pub fn state(& self) -> & Sym { & self.state }
  #[inline(always)]
  pub fn body(& self) -> & Body { & self.body }
}
impl fmt::Display for Pred {
  fn fmt(& self, fmt: & mut fmt::Formatter) -> fmt::Result {
    write!(
      fmt, "{}({}) {{ {} }}", self.sym, self.state, self.body
    )
  }
}

#[derive(Debug,Clone)]
pub struct Init {
  sym: Sym,
  state: Sym,
  body: Body,
}
impl Init {
  #[inline(always)]
  pub fn mk(sym: Sym, state: Sym, body: Body) -> Self {
    Init { sym: sym, state: state, body: body }
  }
  #[inline(always)]
  pub fn sym(& self) -> & Sym { & self.sym }
  #[inline(always)]
  pub fn state(& self) -> & Sym { & self.state }
  #[inline(always)]
  pub fn body(& self) -> & Body { & self.body }
}
impl fmt::Display for Init {
  fn fmt(& self, fmt: & mut fmt::Formatter) -> fmt::Result {
    write!(
      fmt, "{}({}) {{ {} }}", self.sym, self.state, self.body
    )
  }
}

#[derive(Debug,Clone)]
pub struct Trans {
  sym: Sym,
  state: Sym,
  body: Body,
}
impl Trans {
  #[inline(always)]
  pub fn mk(sym: Sym, state: Sym, body: Body) -> Self {
    Trans { sym: sym, state: state, body: body }
  }
  #[inline(always)]
  pub fn sym(& self) -> & Sym { & self.sym }
  #[inline(always)]
  pub fn state(& self) -> & Sym { & self.state }
  #[inline(always)]
  pub fn body(& self) -> & Body { & self.body }
}
impl fmt::Display for Trans {
  fn fmt(& self, fmt: & mut fmt::Formatter) -> fmt::Result {
    write!(
      fmt, "{}({}) {{ {} }}", self.sym, self.state, self.body
    )
  }
}

#[derive(Debug,Clone)]
pub struct Sys {
  sym: Sym,
  state: Sym,
  init: Sym,
  trans: Sym,
}
impl Sys {
  #[inline(always)]
  pub fn mk(sym: Sym, state: Sym, init: Sym, trans: Sym) -> Self {
    Sys { sym: sym, state: state, init: init, trans: trans }
  }
  #[inline(always)]
  pub fn sym(& self) -> & Sym { & self.sym }
  #[inline(always)]
  pub fn state(& self) -> & Sym { & self.state }
  #[inline(always)]
  pub fn init(& self) -> & Sym { & self.init }
  #[inline(always)]
  pub fn trans(& self) -> & Sym { & self.trans }
}
impl fmt::Display for Sys {
  fn fmt(& self, fmt: & mut fmt::Formatter) -> fmt::Result {
    write!(
      fmt, "{}({}) {{ {} -> {} }}",
      self.sym, self.state, self.init, self.trans
    )
  }
}

#[derive(Debug)]
pub enum Item {
  St(State),
  FDc(FunDec),
  FDf(FunDef),
  P(Pred),
  I(Init),
  T(Trans),
  S(Sys),
}
impl Item {
  pub fn sym(& self) -> & Sym {
    use base::Item::* ;
    match * self {
      St(ref bla) => bla.sym(),
      FDc(ref bla) => bla.sym(),
      FDf(ref bla) => bla.sym(),
      P(ref bla) => bla.sym(),
      I(ref bla) => bla.sym(),
      T(ref bla) => bla.sym(),
      S(ref bla) => bla.sym(),
    }
  }
}

pub enum Callable {
  Dec(FunDec),
  Def(FunDef),
}
impl fmt::Display for Callable {
  fn fmt(& self, fmt: & mut fmt::Formatter) -> fmt::Result {
    match * self {
      Callable::Dec(ref f) => write!(fmt, "declaration | {}", f),
      Callable::Def(ref f) => write!(fmt, "definition  | {}", f),
    }
  }
}

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

pub struct Context {
  buffer: String,
  factory: Factory,
  all: HashSet<Sym>,
  states: HashMap<Sym, State>,
  callables: HashMap<Sym, Callable>,
  preds: HashMap<Sym, Pred>,
  inits: HashMap<Sym, Init>,
  transs: HashMap<Sym, Trans>,
  syss: HashMap<Sym, Sys>,
}
impl Context {
  pub fn mk(factory: Factory, buffer: usize) -> Self {
    Context {
      buffer: String::with_capacity(buffer),
      factory: factory,
      all: HashSet::new(),
      states: HashMap::new(),
      callables: HashMap::new(),
      preds: HashMap::new(),
      inits: HashMap::new(),
      transs: HashMap::new(),
      syss: HashMap::new(),
    }
  }

  pub fn lines(& self) -> String {
    let s = format!("buffer: {}", self.buffer) ;
    let s = map_to_lines(& self.callables, "function symbols:", s) ;
    let s = map_to_lines(& self.states, "states:", s) ;
    let s = map_to_lines(& self.preds, "preds:", s) ;
    let s = map_to_lines(& self.inits, "inits:", s) ;
    let s = map_to_lines(& self.transs, "transs:", s) ;
    let s = map_to_lines(& self.syss, "syss:", s) ;
    s
  }

  pub fn bytes(& self) -> & [u8] { self.buffer.as_bytes() }

  pub fn factory(& self) -> & Factory { & self.factory }

  pub fn read(
    & mut self, reader: & mut io::Read
  ) -> io::Result<
    Result<
      Option<(Sym, Vec<Sym>, Vec<Sym>)>,
      (Item,Item)
    >
  > {
    use nom::IResult::* ;
    // use std::mem::swap ;
    use std::io::{ BufRead, BufReader } ;
    use std::str ;
    use parse::{ item_parser, check_parser, exit_parser } ;
    let mut lines = BufReader::new(reader).lines() ;
    let mut buffer = String::with_capacity(self.buffer.capacity()) ;
    // swap(& mut self.buffer, & mut buffer) ;
    // panic!("bla")
    loop {
      let mut new_things = false ;

      // println!("  entering lines loop") ;
      loop {
        match lines.next() {
          Some(Ok(line)) => {
            self.buffer.push('\n') ;
            self.buffer.push_str(& line) ;
            new_things = true
          },
          Some(Err(e)) => {
            return Err(e)
          },
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
          Done(chars, Ok(_)) => {
            self.buffer.clear() ;
            self.buffer.push_str(str::from_utf8(chars).unwrap()) ;
          },
          Done(_, Err((i1,i2))) => return Ok( Err((i1,i2)) ),
          Incomplete(_) => {
            // println!("  incomplete (item)") ;
            break
          },
          _ => match check_parser(buffer.as_bytes(), & self.factory) {
            Done(chars, check) => {
              self.buffer.clear() ;
              self.buffer.push_str(str::from_utf8(chars).unwrap()) ;
              return Ok( Ok( Some(check) ) )
            },
            Incomplete(_) => {
              println!("  incomplete (check)") ;
              break
            },
            _ => match exit_parser(buffer.as_bytes()) {
              Done(_,_) => return Ok( Ok(None) ),
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

  fn check(& self, sym: & Sym) -> Result<(),Item> {
    use self::Item::* ;
    use self::Callable::* ;
    if self.all.contains(sym) {
      match self.states.get(sym) {
        None => (),
        Some(ref state) => return Err( St((* state).clone()) ),
      } ;
      match self.callables.get(sym) {
        None => (),
        Some(& Dec(ref f)) => return Err( FDc(f.clone()) ),
        Some(& Def(ref f)) => return Err( FDf(f.clone()) ),
      } ;
      match self.preds.get(sym) {
        None => (),
        Some(pred) => return Err( P(pred.clone()) ),
      } ;
      match self.inits.get(sym) {
        None => (),
        Some(init) => return Err( I(init.clone()) ),
      } ;
      match self.transs.get(sym) {
        None => (),
        Some(trans) => return Err( T(trans.clone()) ),
      } ;
      match self.syss.get(sym) {
        None => (),
        Some(sys) => return Err( S(sys.clone()) ),
      } ;
      panic!("symbol {:?} is in all but nowhere else", sym)
    } else {
      Ok(())
    }
  }
}

pub trait CanAdd<T> {
  fn add(& mut self, T) -> Result<(),(Item,Item)> ;
}

impl CanAdd<Item> for Context {
  fn add(& mut self, i: Item) -> Result<(),(Item,Item)> {
    use base::Item::* ;
    match i {
      St(bla) => self.add(bla),
      FDc(bla) => self.add(bla),
      FDf(bla) => self.add(bla),
      P(bla) => self.add(bla),
      I(bla) => self.add(bla),
      T(bla) => self.add(bla),
      S(bla) => self.add(bla),
    }
  }
}

macro_rules! impl_add {
  ($input:ident, ($slf:ident, $i:ident) -> $b:block, $err:ident) => (
    impl CanAdd<$input> for Context {
      fn add(& mut $slf, $i: $input) -> Result<(),(Item,Item)> {
        match $slf.check($i.sym()) {
          Ok(()) => {
            $slf.all.insert($i.sym().clone()) ;
            $b ;
            Ok(())
          },
          Err(e) => Err( (Item::$err($i), e) ),
        }
      }
    }
  ) ;
  ($input:ident, $map:ident, $err:ident) => (
    impl_add!{
      $input, (self, i) -> { self.$map.insert(i.sym().clone(), i) }, $err
    }
  )
}

impl_add!{ State, states, St }
impl_add!{
  FunDef,
  (self, i) -> {
    self.callables.insert( i.sym().clone(), Callable::Def(i) )
  },
  FDf
}
impl_add!{
  FunDec,
  (self, i) -> {
    self.callables.insert( i.sym().clone(), Callable::Dec(i) )
  },
  FDc
}
impl_add!{ Pred, preds, P }
impl_add!{ Init, inits, I }
impl_add!{ Trans, transs, T }
impl_add!{ Sys, syss, S }
