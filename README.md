![ebso](doc/logo/logo.svg?sanitize=true)

# An EVM Byte code Super Optimizer

The tool ebso automatically finds optimizations for loop-free Ethereum byte
code.  Therefore ebso employs a method called [unbounded superoptimization
(Jangda & Yorsh,
2017)](http://www.eecs.qmul.ac.uk/~gretay/papers/onward2017.pdf), which relies
on a constraint solver to guarantee correctness of the transformation.  Through
superoptimization ebso automatically finds programs that need less gas, but are
observationally equivalent. The search for these cheaper programs is encoded as
an SMT problem, which ebso solves relying on
[Z3](https://github.com/Z3Prover/z3).

## Installation and Running

The easiest way to install ebso is using [opam](https://opam.ocaml.org/).
Simply run `opam install .` after cloning the repository.
Afterwards one can run `ebso -help` for information on how to call ebso.

## Example
```
$ ./ebso -translation-validation 256 -direct "600003600301"
Optimized PUSH 0 SUB PUSH 3 ADD to
PUSH 3 SUB
Saved 6 gas, translation validation successful,
this instruction sequence is optimal.
```
