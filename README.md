Kinō (帰納: induction, recursion) is an SMT-based, k-induction engine for transition systems.

# Techniques

implemented:

- Bounded Model Checking (`bmc`)
- K-induction (`kind`)

future:

- invariant generation
    - [instantiation-based][graph based invgen]
    - machine-learning-based from [ICE][ice invgen] and [C2I][c2i invgen]
- test generation

# Build and run

Building running etc. follows the standard cargo workflow. A few example
systems can be found in `rsc/tsv/`. For instance

```bash
> cargo run rsc/tsv/modular_four.tsv
```

To run kinō you need a SMT solver installed and in your path.
For now, only [Z3][z3] is supported. It must be in your path with command `z3`.

# License

Copyright 2015 Adrien Champion. See the COPYRIGHT file at the top-level
directory of this distribution.

Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
http://www.apache.org/licenses/LICENSE-2.0> or the MIT license <LICENSE-MIT or
http://opensource.org/licenses/MIT>, at your option.



[graph based invgen]: http://homepage.cs.uiowa.edu/~tinelli/papers/KahGT-NFM-11.pdf (Instantiation-based Invariant Generation)
[ice invgen]: http://web.engr.illinois.edu/~garg11/papers/dt-ice.pdf (ICE Invariant Generation)
[c2i invgen]: http://web.stanford.edu/~sharmar/pubs/c2i.pdf (C2I Invariant Generation)

[z3]: https://github.com/Z3Prover/z3 (Z3 SMT solver)