* Abstract argument of PUSH instructions in encoding by using template; until
  then hardcode arguments

* Add encoding for target programs, i.e., function "instr" that gives
  instruction to be used in round j

* Implement decoder, i.e., model to target program

* Abstract enc_instruction over number of elements added and deleted on stack
