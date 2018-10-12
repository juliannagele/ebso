# ebso: An EVM Byte code Super Optimizer

We aim to apply unbounded super optimization in the style of [Jangda & Yorsh,
 2017](http://www.eecs.qmul.ac.uk/~gretay/papers/onward2017.pdf) to
 loop-free EVM byte code. Through super optimization we hope to
 automatically find programs, which need less gas, but are
 observationally equivalent. We plan to encode the search for these
 cheaper programs as an SMT problem. This SMT problem can then be
 solved by a state-of-the art SMT solver, such as
 [Z3](https://github.com/Z3Prover/z3). For the semantics of EVM byte
 code we look to work by [Amani et al,
 2018](https://dl.acm.org/citation.cfm?doid=3176245.3167084).

## Installation and Running

The easiest way to install ebso is using [opam](https://opam.ocaml.org/).
Simply run `opam install .` after cloning the repository.
Afterwards one can run `ebso -help` for information on how to call ebso.
Currently lists of instructions are given to ebso as S-expressions like
so `((PUSH 0) SUB (PUSH 3) ADD)`.
