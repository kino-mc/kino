// Copyright 2015 Adrien Champion. See the COPYRIGHT file at the top-level
// directory of this distribution.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! Logging. */

use ansi::Style as AStyle ;

use term::{ Sym, Offset } ;

use sys::Cex ;

/// Formatting elements of a log.
pub trait Formatter: Clone {
  /// The pre prefix.
  #[inline(always)]
  fn ppre(& self) -> & str ;
  /// The prefix.
  #[inline(always)]
  fn pref(& self) -> & str ;
  /// The header.
  #[inline(always)]
  fn head(& self) -> & str ;
  /// The trailer.
  #[inline(always)]
  fn trail(& self) -> & str ;
}

/// No formatting.
#[derive(Clone)]
pub struct NoFormat ;
impl Formatter for NoFormat {
  fn ppre(& self) -> & str { & "" }
  fn pref(& self) -> & str { & "" }
  fn head(& self) -> & str { & "" }
  fn trail(& self) -> & str { & "" }
}

/// Custom formatting.
#[derive(Clone)]
pub struct Format {
  /// The pre prefix.
  ppre: & 'static str,
  /// The prefix.
  pref: & 'static str,
  /// The header.
  head: & 'static str,
  /// The trailer.
  trail: & 'static str,
}
impl Format {
  /// Default formatter.
  pub fn default() -> Self {
    Format {
      ppre: ";", pref: "|", head: "=====|", trail: "=====|"
    }
  }
}
impl Formatter for Format {
  fn ppre(& self) -> & str { self.ppre }
  fn pref(& self) -> & str { self.pref }
  fn head(& self) -> & str { self.head }
  fn trail(& self) -> & str { self.trail }
}



/// Style things for printing.
pub trait Styler: Clone {
  /// Emphasizes something.
  #[inline]
  fn emph(& self, & str) -> String ;
  /// Makes something happy (success).
  #[inline]
  fn happy(& self, & str) -> String ;
  /// Makes something sad (warning).
  #[inline]
  fn sad(& self, & str) -> String ;
  /// Makes something bad (error).
  #[inline]
  fn bad(& self, & str) -> String ;
}

/// No styling.
#[derive(Clone)]
pub struct NoStyle ;
impl Styler for NoStyle {
  fn emph(& self, s: & str) -> String { s.to_string() }
  fn happy(& self, s: & str) -> String { s.to_string() }
  fn sad(& self, s: & str) -> String { s.to_string() }
  fn bad(& self, s: & str) -> String { s.to_string() }
}

/// Custom styling.
#[derive(Clone)]
pub struct Style {
  /// Emphasis style.
  em: AStyle,
  /// Happy style.
  ha: AStyle,
  /// Sad style.
  sa: AStyle,
  /// Bad style.
  ba: AStyle
}
impl Style {
  /// Default style.
  pub fn default() -> Self {
    use ansi::Colour::* ;
    Style {
      em: AStyle::new().bold(),
      ha: Green.bold(),
      sa: Yellow.bold(),
      ba: Red.bold(),
    }
  }
}
impl Styler for Style {
  fn emph(& self, s: & str) -> String {
    format!("{}", self.em.paint(s))
  }
  fn happy(& self, s: & str) -> String {
    format!("{}", self.ha.paint(s))
  }
  fn sad(& self, s: & str) -> String {
    format!("{}", self.sa.paint(s))
  }
  fn bad(& self, s: & str) -> String {
    format!("{}", self.ba.paint(s))
  }
}



/// Logger used by kino at top level.
#[derive(Clone)]
pub struct MasterLog<F, S> {
  /// Formatting.
  fmt: F,
  /// Styling.
  stl: S,
}

impl<F, S: Clone> MasterLog<F, S> {
  /// A clone of the styler of a log.
  pub fn styler(& self) -> S { self.stl.clone() }
  /// The formatter.
  #[inline(always)]
  pub fn fmt(& self) -> & F { & self.fmt }
  /// The styler.
  #[inline(always)]
  pub fn stl(& self) -> & S { & self.stl }
}

impl MasterLog<Format, Style> {
  /// Creates a default log.
  pub fn default() -> Self {
    MasterLog { fmt: Format::default(), stl: Style::default() }
  }
}

impl MasterLog<NoFormat, NoStyle> {
  /// Creates a no formatting, no styling log.
  pub fn empty() -> Self {
    MasterLog { fmt: NoFormat, stl: NoStyle }
  }
}

impl<F: Formatter, S: Styler> Styler for MasterLog<F, S> {
  fn emph(& self, s: & str) -> String { self.stl.emph(s) }
  fn happy(& self, s: & str) -> String { self.stl.happy(s) }
  fn sad(& self, s: & str) -> String { self.stl.sad(s) }
  fn bad(& self, s: & str) -> String { self.stl.bad(s) }
}

impl<
  F: Formatter,
  S: Styler,
> MasterLog<F, S> {
  /// Emphasizes something.
  pub fn mk_emph(& self, s: & str) -> String { self.stl.emph(s) }
  /// Makes something happy.
  pub fn mk_happy(& self, s: & str) -> String { self.stl.happy(s) }
  /// Makes something sad.
  pub fn mk_sad(& self, s: & str) -> String { self.stl.sad(s) }
  /// Makes something bad.
  pub fn mk_bad(& self, s: & str) -> String { self.stl.bad(s) }

  /// Prints a separation between log sections.
  pub fn sep(& self) {
    println!("")
  }

  /// Prints a newline in a log section.
  pub fn nl(& self) {
    println!("{} {}", self.fmt.ppre(), self.fmt.pref())
  }

  /// Prints a trailer line.
  pub fn trail(& self) {
    println!("{} {}{}", self.fmt.ppre(), self.fmt.pref(), self.fmt.trail()) ;
    self.sep()
  }

  /// Prints a title line.
  pub fn title(& self, e: & str) {
    println!(
      "{} {}{} {}",
      self.fmt.ppre(), self.fmt.pref(), self.fmt.head(), self.mk_emph(e)
    )
  }

  /// Prints some log lines.
  pub fn print(& self, e: & str) {
    for line in e.lines() {
      println!("{} {} {}", self.fmt.ppre(), self.fmt.pref(), line)
    }
  }

  /// Logs something with a prefix.
  pub fn pref_log(
    & self, pref: & str, title: & super::Tek, bla: & str
  ) {
    println!(
      "{} {} {}", self.fmt.ppre(), pref, self.emph(title.to_str())
    ) ;
    for line in bla.lines() {
      println!("{} {}   {}", self.fmt.ppre(), pref, line)
    }
  }

  /// Logs some text line by line.
  pub fn log(& self, t: & super::Tek, bla: & str) {
    self.pref_log(self.fmt.pref(), t, bla) ;
    self.nl()
  }

  /// Prints some happy text line by line.
  pub fn happy(& self, t: & super::Tek, bla: & str) {
    self.pref_log( & self.mk_happy( self.fmt.pref() ), t, bla ) ;
    self.nl()
  }

  /// Prints some sad text line by line.
  pub fn sad(& self, t: & super::Tek, bla: & str) {
    self.pref_log( & self.mk_sad( self.fmt.pref() ), t, bla ) ;
    self.nl()
  }

  /// Prints some bad text line by line.
  pub fn bad(& self, t: & super::Tek, bla: & str) {
    self.pref_log( & self.mk_bad( self.fmt.pref() ), t, bla ) ;
    self.nl()
  }

  /// Alias for `bad(& Tek::Kino, blah)`, to make `MasterLog` compatible with
  /// `try_error!`.
  pub fn error(& self, bla: & str) {
    self.bad(& super::Tek::Kino, bla)
  }

  /// Does nothing, to make `MasterLog` compatible with `try_error!`.
  pub fn done<T>(& self, _: T) {}

  /// Logs a `safe` end of analysis.
  pub fn log_safe(& self) {
    let pref = format!(
      "{} {}",
      self.fmt.ppre(),
      self.mk_happy( self.fmt.pref() )
    ) ;
    println!(
      "{} {}",
      pref, self.mk_happy( "done, system is safe")
    ) ;
    println!("{}", pref) ;
    println!("safe") ;
    self.nl()
  }

  /// Logs an `unsafe` end of analysis.
  pub fn log_unsafe(& self) {
    let pref = format!(
      "{} {}",
      self.fmt.ppre(),
      self.mk_bad( self.fmt.pref() )
    ) ;
    println!(
      "{} {}",
      pref,
      self.mk_bad( "done, system is unsafe")
    ) ;
    println!("{}", pref) ;
    println!("unsafe") ;
    self.nl()
  }

  /// Logs a `unknown` end of analysis.
  pub fn log_unknown<
    'a, Props: Iterator<Item = & 'a Sym>
  >(& self, props: Props) {
    let pref = format!(
      "{} {}",
      self.fmt.ppre(),
      self.mk_sad( self.fmt.pref() )
    ) ;
    println!(
      "{} {}",
      pref,
      self.mk_sad( "done, analysis was inconclusive")
    ) ;
    println!(
      "{} could not (dis)prove",
      pref
    ) ;
    for prop in props {
      println!(
        "{} - {}",
        pref,
        self.mk_sad( & format!("{}", prop) )
      )
    } ;
    println!("{}", pref) ;
    println!("unknown") ;
    self.nl()
  }

  /// Logs a `unknown` end of analysis without any unknown properties.
  pub fn just_log_unknown(& self) {
    let pref = format!(
      "{} {}",
      self.fmt.ppre(),
      self.mk_sad( self.fmt.pref() )
    ) ;
    println!(
      "{} {}",
      pref,
      self.mk_sad( "done, analysis was inconclusive")
    ) ;
    println!("{}", pref) ;
    println!("unknown") ;
    self.nl()
  }

  /// Logs the fact that a property proved some techniques.
  pub fn log_proved(
    & self, t: & super::Tek, props: & [Sym], info: & Offset
  ) {
    let pref = format!(
      "{} {}", self.fmt.ppre(), self.mk_happy(self.fmt.pref())
    ) ;
    println!(
      "{} {} proved {} propertie(s) at {}:",
      pref, self.emph(t.desc()), props.len(), info
    ) ;
    println!("{}", pref) ;
    println!("(proved") ;
    for prop in props.iter() {
      println!("  {}", prop.sym()) ;
      // println!("{}   {}", pref, self.mk_happy(prop.sym())) ;
    } ;
    println!(")") ;
    self.nl()
  }

  /// Logs a cex for some properties.
  pub fn log_cex(
    & self, t: & super::Tek, cex: & Cex, props: & [Sym]
  ) {
    use std::io::stdout ;
    let pref = format!(
      "{} {}", self.fmt.ppre(), self.mk_bad(self.fmt.pref())
    ) ;
    println!(
      "{} {} falsified {} propertie(s) at {}:",
      pref, self.emph(t.to_str()), props.len(), cex.len()
    ) ;
    for prop in props.iter() {
      println!("{}   {}", pref, self.mk_bad(prop.sym())) ;
    } ;
    println!("{} {}:", pref, self.mk_emph("cex")) ;
    // for line in cex.format().lines() {
    //   println!("{}   {}", pref, line)
    // } ;
    println!("{}", pref) ;
    cex.write_vmt(props, & mut stdout()).expect(
      "could not write counterexample to stdout"
    ) ;
    self.nl()
  }
}