Kinō (帰納: induction, recursion) is an SMT-based, k-induction engine for transition systems.

**NB: kino is not maintained anymore for now, for lack of time. If you are interested in this project please open an issue or contact me directly.**

**⚠️ Also, the current (and probably last) version of kino relies on an old version of the `hashconsing` crate, which has [security vulnerabilities][cve].**

# Code status

[![Build Status](https://travis-ci.org/kino-mc/kino.svg?branch=master)](https://travis-ci.org/kino-mc/kino)

- builds: debug, release
- platforms: linux, osx, windows
- tests: none

# About

`kino` is a re-implementation from scratch, in Rust, of the core verification
engine of [Kind 2 model-checker](https://kind2-mc.github.io/kind2/). Unlike
Kind 2 however, `kino` does not read Lustre files: it deals with system
expressed in the VMT-LIB standard (to be published).

# Solvers

supported:

- z3 -- 4.4.2+, not guaranteed to work for older versions

future:

- CVC4

# Techniques

implemented:

- Bounded Model Checking (`bmc`)
- K-induction (`kind`)
- 2-induction (`twind`)
- template-based invariant generation (`tig`)
    - one-state candidates only
    - bool candidates only
- invariant pruner (`pruner`)

future:

- invariant generation
    - two-state candidates
    - arith candidates

# Build and run

To run kinō you need a SMT solver installed and in your path. For now, only
[Z3][z3] is supported. It must be in your path with command `z3`, although you
can tell kinō to use your own using the CLAs.

Building running etc. follows the standard cargo workflow. A few example
systems can be found in `rsc/simple/` and `rsc/from_kind`. For instance

```bash
> cargo run rsc/simple/modular_four.vmt
```

(This will run kinō in `debug` mode, which is **extremely** slower than in
`release` because of all the runtime checks performed in `debug`.)

## Tests

(Almost) all systems in `rsc` are associated with a test in `tests/`. However
currently cargo behaves oddly with kinō, and is very much non-deterministic.
This seems to come from the heavy use of parallelism in kinō.

# NB

As of right now `kino` is not deterministic. This is due to the hashing
algorithm (sip) which is the only stable one in Rust right now. The
[`hashconsing` crate](https://crates.io/crates/hashconsing) relies on this
algorithm to hashcons symbols, terms, *etc.* and this algorithm is not
deterministic.

As a result, terms (in particular properties) may not be printed in the same
order whenever printing is done by iterating over a set / hash map. This causes
a very slightly different problem to be given to the solver, which might cause
the solver to return different models. (This is known to happen for z3.)

# License

Copyright 2016 Adrien Champion. See the COPYRIGHT file at the top-level
directory of this distribution.

Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
http://www.apache.org/licenses/LICENSE-2.0> or the MIT license <LICENSE-MIT or
http://opensource.org/licenses/MIT>, at your option.



[graph based invgen]: http://homepage.cs.uiowa.edu/~tinelli/papers/KahGT-NFM-11.pdf (Instantiation-based Invariant Generation)
[ice invgen]: http://web.engr.illinois.edu/~garg11/papers/dt-ice.pdf (ICE Invariant Generation)
[c2i invgen]: http://web.stanford.edu/~sharmar/pubs/c2i.pdf (C2I Invariant Generation)

[z3]: https://github.com/Z3Prover/z3 (Z3 SMT solver)
[cve]: https://nvd.nist.gov/vuln/detail/CVE-2020-36215