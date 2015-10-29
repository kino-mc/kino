/** Term factory stuff. */

use smt::ParseSmt2 ;

use ::sym::* ;
use ::term::* ;

struct Factory {
  sym: SymConsign,
  term: TermConsign,
}

// impl ParseSmt2 for Factory {
//   type Ident = id::Id ;
//   type Value = 
// }