* Add encoding of gas consumption; plan: add func_decl gas to state
  of type int -> int that records accumulated gas consumption up
  to instruction j

* Add functionality to encode source programs;
  plan: foldi opcode encoding over list of source instructions

* Abstract argument of PUSH instructions in encoding by using template; until
  then hardcode arguments

* Add encoding for target programs, i.e., function "instr" that gives
  instruction to be used in round j

* Implement decoder, i.e., model to target program
