# ebso: An EVM Bytecode Super Optimizer

We aim to apply super optimization in the style of [Jangda & Yorsh,
 2017](http://www.eecs.qmul.ac.uk/~gretay/papers/onward2017.pdf) to
 loop-free EVM byte code. Through super optimization we hope to
 automatically find programs, which need less gas, but are
 observationally equvivalent. We plan to encode the search for these
 cheaper programs as an SMT problem. This SMT problem can then be
 solved by a state-of-the art SMT solver, such as
 [Z3](https://github.com/Z3Prover/z3). For the semantics of EVM byte
 code we look to work by [Amani et al,
 2018](https://dl.acm.org/citation.cfm?doid=3176245.3167084).

## authors

[Julian Nagele](https://jnagele.net/) &
[Maria A Schett](http://maria-a-schett.net/)
