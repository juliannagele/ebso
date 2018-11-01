* Encode remaining instructions

* Encode instructions such as GASPRICE or BLOCKHASH, which are basically pushing 
  an unknown number onto the stack, by PUSH (Const y) and forall quantification
  over all ys, similar to initial stack arguments

* Encodings of if possible? Conjecture: unbounded super optimization
  outperforms super optimization

* Refactor evmenc; split into modules

* Implement "normal" superoptimization: enumerate candidate programs and test
  for equivalence

* Improve bound on number of instructions in target program to allow solver to prove
  optimality (currently: gas cost of source program)

* Collect benchmarks: SMT and EVM bytecode snippets
  * open Zeppelin: compile with and without optimization with solc
  * get contracts from blockchain (filter out garbage)

* Bitblasting performance problem:
  * check CAV 2015 paper (and journal version)
  * change BVs to Ints
  * try vampire
  * generate candidate program by instantiating quantifier and then check
    equivalence

* Regression tests
  * geth debugger
  * actual blockchain (what do we compare? what about hashes that changed?)

* Set up experiments/evaluation
  * output format
  * how to keep connection between benchmarks and contracts they are from
  * where to run?
