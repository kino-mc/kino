/*!

## TODO

`num::rational` crash if denominator is zero. Can happen in parser. Parsing
only non-zero denominator will push the problem to function symbol application.

*/

extern crate num ;
extern crate hashconsing as hcons ;
#[macro_use]
extern crate nom ;

mod base ;
pub mod typ ;
pub mod sym ;
pub mod id ;
pub mod term ;
pub mod parse ;

pub use base::* ;
