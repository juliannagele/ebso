(*   Copyright 2019 Julian Nagele and Maria A Schett

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)
open OUnit2
open Ebso
open Instruction.T
open Enc_consts

let suite =
  "suite" >:::
  [
    "convert between opcode and instruction">:: (fun _ ->
        let ea = Enc_consts.mk [] (`User [SUB; ADD; POP]) in assert_equal ~cmp:[%eq: Instruction.t] ~printer:[%show: Instruction.t]
          ADD (Opcode.to_instr ea.opcodes (Opcode.from_instr ea.opcodes ADD))
      );
]

let () =
  run_test_tt_main suite
