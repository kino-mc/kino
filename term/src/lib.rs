/*!

## TODO

`num::rational` crash if denominator is zero. Can happen in parser. Parsing
only non-zero denominator will push the problem to function symbol application.

*/

extern crate num ;
#[macro_use]
extern crate nom ;
extern crate hashconsing as hcons ;
extern crate rsmt2 as smt ;

mod base ;
pub mod typ ;
pub mod sym ;
// pub mod id ;
pub mod cst ;
pub mod term ;
pub mod parser ;
pub mod factory ;

pub use base::* ;
