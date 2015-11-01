// Copyright 2015 Adrien Champion. See the COPYRIGHT file at the top-level
// directory of this distribution.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

extern crate term ;

use term::{ Sym, Type, Term } ;

pub struct Sig {
  vars: Vec<Type>,
}
pub struct NamedSig {
  vars: Vec<(Sym, Type)>,
}

pub struct State {
  sym: Sym,
  sig: NamedSig,
}

pub struct Body {
  body: Vec<Term>,
  calls: Vec<Sym>,
}

pub struct FunDec {
  sym: Sym,
  sig: Sig,
  typ: Type,
}

pub struct FunDef {
  sym: Sym,
  sig: NamedSig,
  typ: Type,
  body: Body,
}

pub struct Pred {
  sym: Sym,
  state: Sym,
}

pub struct Sys {
  sym: Sym,
  state: State,
  body: Body,
}