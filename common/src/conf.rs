// Copyright 2015 Adrien Champion. See the COPYRIGHT file at the top-level
// directory of this distribution.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

/*! Option handling stuff. */

use nom::{ multispace, IResult } ;

use term::smt::SolverStyle ;

use log::{ Formatter, Styler, MasterLog } ;

/// Can be printed.
trait Print {
  /// String representation.
  fn to_str(& self) -> String ;
}
/// Can parse itself.
trait Parse: Sized {
  /// Parses itself.
  fn of(& str) -> Result<Self, String> ;
}

/// A configuration item.
struct ConfItem<T> {
  /// The key identifying the option.
  key: & 'static str,
  /// Legal values the key can take.
  shrt: String,
  /// Description of the configuration item.
  long: String,
  /// Value of the configuration item.
  val: T,
}

impl<T: Print + Parse> ConfItem<T> {
  /** Creates a new configuration item.

  - `key`: key identifying the option
  - `shrt`: legal values the key can take
  - `long`: description of the configuration item
  - `val`: value of the item
  */
  pub fn mk(
    key: & 'static str, shrt: String, long: String, val: T
  ) -> Self {
    ConfItem { key: key, shrt: shrt, long: long, val: val }
  }
  /// Line description of an item.
  pub fn lines<
    F: Formatter, S: Styler
  >(& self, fmt: & F, stl: & S) -> Vec<String> {
    let mut vec = Vec::with_capacity(self.long.len() + 1) ;
    vec.push(
      format!(
        "{} {}: {}", fmt.pref(), stl.emph(self.key), & self.shrt
      )
    ) ;
    vec.push( format!("{}    Default: {}", fmt.pref(), self.val.to_str()) ) ;
    for line in self.long.lines() {
      vec.push( format!("{}    {}", fmt.pref(), line) )
    } ;
    vec
  }
  // /// Sets the value of a configuration item.
  // pub fn set(& mut self, val: & str) -> Result<(), String> {
  //   match T::of(val) {
  //     Ok(val) => { self.val = val ; Ok(()) },
  //     Err(e) => Err(e),
  //   }
  // }
}



impl Print for usize {
  fn to_str(& self) -> String { format!("{}", self) }
}
impl Parse for usize {
  fn of(val: & str) -> Result<usize, String> {
    match val.parse::<usize>() {
      Ok(val) => Ok(val),
      Err(_) => Err(
        format!("expected int, got {}", val)
      ),
    }
  }
}

impl Print for bool {
  fn to_str(& self) -> String { format!("{}", self) }
}
impl Parse for bool {
  fn of(val: & str) -> Result<bool, String> {
    match val {
      "on" | "true" => Ok(true),
      "off" | "false" => Ok(false),
      _ => Err(
        format!("expected bool [on/true/off/false], got {}", val)
      ),
    }
  }
}

impl Print for SolverStyle {
  fn to_str(& self) -> String { self.cmd() }
}
impl Parse for SolverStyle {
  fn of(val: & str) -> Result<SolverStyle, String> {
    match SolverStyle::of_str(val) {
      Some(val) => Ok(val),
      None => Err(
        format!(
          "unknown solver style \"{}\"", val
        )
      ),
    }
  }
}

impl Print for String {
  fn to_str(& self) -> String { self.clone() }
}
impl Parse for String {
  fn of(val: & str) -> Result<String, String> {
    Ok(val.to_string())
  }
}

impl<T: Print> Print for Option<T> {
  fn to_str(& self) -> String {
    match * self {
      Some(ref val) => val.to_str(),
      None => "none".to_string(),
    }
  }
}
impl<T: Parse> Parse for Option<T> {
  fn of(val: & str) -> Result<Option<T>, String> {
    match val {
      "none" => Ok(None),
      val => match T::of(val) {
        Ok(val) => Ok( Some(val) ),
        Err(e) => Err(
          format!("expected bool, got {} ({:?})", val, e)
        ),
      },
    }
  }
}



trait HasSet {
  /// Sets the value of a configuration item.
  fn set(& mut self, & str, & str) -> Result<(), String> ;
}



/// Creates a configuration structure.
macro_rules! conf {
  ($name:ident ($head:expr) {
    $( $item:ident(
      $typ:ty,
      $key:expr,
      $shrt:expr,
      $long:expr,
      $default:expr,
      $val:ident => $parser:expr
    ) ),+
  } ) => (
    /// Configuration structure.
    pub struct $name {
      head: String,
      $( $item: ConfItem<$typ> ),+
    }
    impl $name {
      /// Default configuration.
      pub fn default() -> Self {
        $name {
          head: $head,
          $( $item: ConfItem::mk($key, $shrt, $long, $default), )+
        }
      }
      /// Multi-line description of the conf structure.
      pub fn lines<
        F: Formatter, S: Styler
      >(fmt: & F, stl: & S) -> Vec<String> {
        let conf = $name::default() ;
        let mut vec = vec![] ;
        vec.push(
          format!("{}{} {}", fmt.pref(), fmt.head(), stl.sad(& conf.head))
        ) ;
        $(
          for line in conf.$item.lines(fmt, stl) {
            vec.push( line.to_string() )
          } ;
        )+
        vec.push(
          format!("{}{}", fmt.pref(), fmt.trail())
        ) ;
        vec
      }
      $(
        /// Accessor.
        #[inline(always)]
        pub fn $item(& self) -> & $typ {
          & self.$item.val
        }
      )+
    }
    impl HasSet for $name {
      fn set(& mut self, key: & str, val: & str) -> Result<(), String> {
        match (key, val) {
          $( ($key, $val) => match $parser {
            Ok(val) => {
              self.$item.val = val ;
              Ok(())
            },
            Err(e) => Err(e),
          }, )+
          _ => Err(
            format!("unknown key \"{}\"", key)
          ),
        }
      }
    }
  )
}

fn solver_keys() -> String {
  SolverStyle::str_keys().iter().fold(
    String::new(), |s, key| format!("{}|{}", s, key)
  )
}


conf!{
  Bmc("Bounded Model Checking (BMC) options".to_string()) {
    is_on (
      bool,
      "turn", "[on/off]".to_string(),
      "(De)activates BMC.".to_string(),
      true,
      val => bool::of(val)
    ),
    max (
      Option<usize>,
      "max", "<int>".to_string(),
      "Maximum number of unrollings.".to_string(),
      None,
      val => Option::<usize>::of(val)
    ),
    smt (
      SolverStyle,
      "smt", solver_keys(),
      "Kind of solver to use.".to_string(),
      SolverStyle::Z3,
      val => SolverStyle::of(val)
    ),
    smt_cmd (
      Option<String>,
      "smt_cmd", "<cmd>".to_string(),
      "Command to run the solver with.".to_string(),
      None,
      val => Option::<String>::of(val)
    ),
    smt_log (
      Option<String>,
      "smt_log", "<file>".to_string(),
      "File to log the smt trace to.".to_string(),
      None,
      val => Option::<String>::of(val)
    )
  }
}


conf!{
  Kind("K-induction (Kind) options".to_string()) {
    is_on (
      bool,
      "turn", "[on/off]".to_string(),
      "(De)activates Kind.".to_string(),
      true,
      val => bool::of(val)
    ),
    max (
      Option<usize>,
      "max", "<int>".to_string(),
      "Maximum number of unrollings.".to_string(),
      None,
      val => Option::<usize>::of(val)
    ),
    smt (
      SolverStyle,
      "smt", solver_keys(),
      "Kind of solver to use.".to_string(),
      SolverStyle::Z3,
      val => SolverStyle::of(val)
    ),
    smt_cmd (
      Option<String>,
      "smt_cmd", "<cmd>".to_string(),
      "Command to run the solver with.".to_string(),
      None,
      val => Option::<String>::of(val)
    ),
    smt_log (
      Option<String>,
      "smt_log", "<file>".to_string(),
      "File to log the smt trace to.".to_string(),
      None,
      val => Option::<String>::of(val)
    )
  }
}


conf!{
  Tig("Template-based Invariant Generation (TIG) options".to_string()) {
    is_on (
      bool,
      "turn", "[on/off]".to_string(),
      "(De)activates TIG.".to_string(),
      true,
      val => bool::of(val)
    ),
    max (
      Option<usize>,
      "max", "<int>".to_string(),
      "Maximum number of unrollings.".to_string(),
      None,
      val => Option::<usize>::of(val)
    ),
    smt (
      SolverStyle,
      "smt", solver_keys(),
      "Kind of solver to use.".to_string(),
      SolverStyle::Z3,
      val => SolverStyle::of(val)
    ),
    smt_cmd (
      Option<String>,
      "smt_cmd", "<cmd>".to_string(),
      "Command to run the solver with.".to_string(),
      None,
      val => Option::<String>::of(val)
    ),
    smt_log (
      Option<String>,
      "smt_log", "<file>".to_string(),
      "File to log the smt trace to.".to_string(),
      None,
      val => Option::<String>::of(val)
    )
  }
}



macro_rules! extend {
  ($vec:ident with $conf:ident) => (
    match $conf {
      Some(conf) => $vec.extend( conf::lines() ),
      None => (),
    }
  )
}

named! {
  string<String>,
  map!(
    is_not!(" ():,"),
    |bytes| ::std::str::from_utf8(bytes).unwrap().to_string()
  )
}

named! {
  option<(String, String)>,
  chain!(
    key: string ~
    // delimited!( opt!(multispace), char!(':'), opt!(multispace) ) ~
    multispace ~
    val: string,
    || (key, val)
  )
}

named! {
  comma_sep<char>,
  delimited!( opt!(multispace), char!(','), opt!(multispace) )
}

named! {
  options< Vec<(String, String)> >,
  delimited!(
    opt!(multispace),
    separated_list!( comma_sep, option ),
    opt!(multispace)
  )
}

named! {
  option_parser<
    Vec< (Option<String>, Vec< (String, String) >) >
  >,

  separated_nonempty_list!(

    comma_sep,

    alt!(

      map!(option, |o| (None, vec![o])) |

      chain!(
        opt!(multispace) ~
        scope: string ~
        delimited!(
          opt!(multispace), char!('('), opt!(multispace)
        ) ~
        opts: options ~
        delimited!(
          opt!(multispace), char!(')'), opt!(multispace)
        ),
        || ( Some(scope), opts )
      )

    )
  )
}

/// Top level configuration.
pub struct Master {
  /// All the technique scopes.
  scopes: Vec<& 'static str>,
  /// Optional BMC configuration.
  pub bmc: Option<Bmc>,
  /// Optional Kind configuration.
  pub kind: Option<Kind>,
  /// Optional TIG configuration.
  pub tig: Option<Tig>,
}
impl Master {
  /// The scope to technique mapping.
  fn set(
    mut self, scope: & str, opts: & [ (String, String) ]
  ) -> Result<Self, (String, Self)> {
    match scope {
      "bmc" => {
        let mut bmc = self.bmc.unwrap_or_else(|| Bmc::default()) ;
        for & (ref key, ref val) in opts.iter() {
          match bmc.set(key, val) {
            Ok(()) => (),
            Err(e) => {
              self.bmc = Some(bmc) ;
              return Err( (e, self) )
            },
          }
        } ;
        self.bmc = Some(bmc) ;
        Ok(self)
      },
      "kind" => {
        let mut kind = self.kind.unwrap_or_else(|| Kind::default()) ;
        for & (ref key, ref val) in opts.iter() {
          match kind.set(key, val) {
            Ok(()) => (),
            Err(e) => {
              self.kind = Some(kind) ;
              return Err( (e, self) )
            },
          }
        } ;
        self.kind = Some(kind) ;
        Ok(self)
      },
      "tig" => {
        let mut tig = self.tig.unwrap_or_else(|| Tig::default()) ;
        for & (ref key, ref val) in opts.iter() {
          match tig.set(key, val) {
            Ok(()) => (),
            Err(e) => {
              self.tig = Some(tig) ;
              return Err( (e, self) )
            },
          }
        } ;
        self.tig = Some(tig) ;
        Ok(self)
      },
      "all" => {
        // println!("all") ;
        let scopes = self.scopes.clone() ;
        let mut res = self ;
        for opt in opts.iter() {
          // println!(" opt: {:?}", opt) ;
          let mut one_ok = false ;
          for scope in scopes.iter() {
            // println!("  scope: {} ({})", scope, one_ok) ;
            res = match res.set(
              scope, & [ (opt.0.to_string(), opt.1.to_string()) ]
            ) {
              Ok(res) => { one_ok = true ; res },
              Err( (_, res) ) => res,
            } ;
          } ;
          if ! one_ok {
            return Err( (
              format!("unknown option/value pair \"{}: {}\"", opt.0, opt.1),
              res
            ) )
          }
        } ;
        Ok(res)
      },
      _ => Err( (
        format!("unknown technique scope \"{}\"", scope),
        self
      ) ),
    }
  }

  /// Default top level configuration.
  fn default() -> Self {
    Master {
      scopes: vec![ "bmc", "kind", "tig" ],
      bmc: Some( Bmc::default() ),
      kind: Some( Kind::default() ),
      tig: Some( Tig::default() ),
    }
  }

  /// Creates the top level configuration by parsing CLAs.
  pub fn mk<
    F: Formatter, S: Styler
  >(log: & MasterLog<F,S>) -> Result<(Self, String), String> {
    let mut args = ::std::env::args() ;
    let mut conf = Master::default() ;
    args.next() ;
    loop {
      if let Some(nxt) = args.next() {
        if "-o" == nxt {
          use nom::{ Err, Needed } ;
          match args.next() {
            Some(options) => {
              match option_parser(options.as_bytes()) {
                IResult::Done(_, opts) => for opt in opts {
                  match opt {
                    (None, args) => match conf.set("all", & args) {
                      Ok(c) => conf = c,
                      Err( (e, _) ) => return Err(e),
                    },
                    (Some(scope), args) => match conf.set(& scope, & args) {
                      Ok(c) => conf = c,
                      Err( (e, _) ) => return Err(e),
                    },
                  }
                },
                IResult::Error(
                  Err::Position(err, p)
                ) => return Err(
                  format!(
                    "could not parse options \"{}\":\n{:?}\n{}",
                    options, err,
                    String::from_utf8_lossy(p)
                  )
                ),
                IResult::Error(e) => return Err(
                  format!("could not parse options \"{}\":\n{}", options, e)
                ),
                IResult::Incomplete(n) => return Err(
                  format!(
                    "incomplete ({}) options \"{}\"",
                    match n {
                      Needed::Unknown => format!("_"),
                      Needed::Size(n) => format!("{}", n),
                    },
                    options
                  )
                ),
              }
            },
            None => return Err(
              "expected options after \"-o\", found nothing".to_string()
            ),
          }
        } else {
          if "-h" == nxt || "--help" == nxt {
            let scope = if let Some(next) = args.next() {
              next.to_string()
            } else { "".to_string() } ;
            Master::help(& scope, log) ;
            log.sep() ;
            log.sep() ;
            ::std::process::exit(0)
          } else {
            let file = nxt ;
            if let Some(nxt) = args.next() {
              return Err(
                format!(
                  "unexpected param \"{}\" after path to file \"{}\"",
                  nxt, file
                )
              )
            } else {
              return Ok( (conf, file.to_string()) )
            }
          }
        }
      } else {
        return Err(
          "unexpected end of parameters, no file specified".to_string()
        )
      }
    }
  }

  /// Scoped help.
  pub fn help<
    F: Formatter, S: Styler
  >(
    scope: & str, log: & MasterLog<F,S>
  ) {

    match scope {
      "bmc" => for line in Bmc::lines(log.fmt(), log.stl()) {
        println!("{}", line)
      },
      "kind" => for line in Kind::lines(log.fmt(), log.stl()) {
        println!("{}", line)
      },
      "tig" => for line in Tig::lines(log.fmt(), log.stl()) {
        println!("{}", line)
      },
      "all" => {
        let mut fst = true ;
        for scope in Master::default().scopes {
          if fst {
            fst = false
          } else {
            log.sep()
          } ;
          Master::help(scope, log) ;
        }
      },
      _ => {

        let scopes = Master::default().scopes.into_iter().fold(
          String::new(),
          |s, scope| format!(
            "{}{}{}",
            s, if s.is_empty() { "" } else { ", " }, log.mk_emph(scope)
          )
        ) ;

        log.title("Usage:") ;
        log.nl() ;
        log.pref_log(
          log.fmt().pref(),
          & super::Tek::Tec("> kino [option]* file", ""),
          & format!("\
where [option] can be
  {} [module]
      Displays this message if no module is specified. Otherwise displays the
      help of the module specified, among
      > {}
  {} \"[ <opt> <val> | <mdl>([<opt> <val>],+) ],+\"
      Sets some options globally (first version) or for a specific module
      (second version). Check the options of each module for more details.
      {}:
      > kino -o \"smt_log: path/to/log, bmc(max: 7, solver: cvc4)\"
      Activates log of the solver's trace for all modules, and option `max`
      (`solver`) in the `bmc` module to `7` (`cvc4`).\
            ",
            log.mk_emph("-h / --help"),
            scopes,
            log.mk_emph("-o"),
            log.mk_emph("Example")
          )
        ) ;
        log.nl() ;
        log.trail()

      }
    }
  }
}











