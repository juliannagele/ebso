(*   Copyright 2018 Julian Nagele and Maria A Schett

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
open Z3util
open Instruction.T
open Superoptimization

module SI = Stack_index

let suite =
  (* set to realistic values for validation *)
  Word.set_wsz 256; SI.set_sas 10;
  "suite" >:::
  [
    (* translation validation *)

    "show equivalence of 3 + (0 - x) and (3 - x)" >::(fun _ ->
        let sp = [PUSH (Word (Val "0")); SUB; PUSH (Word (Val "3")); ADD;] in
        let tp =  [PUSH (Word (Val "3")); SUB] in
        let ea = Enc_consts.mk sp `All in
        let c = enc_trans_val ea tp in
        assert_bool "not unsat" (is_unsat [c])
      );

    "show difference of 3 + (0 - x) and (4 - x)" >::(fun _ ->
        let sp = [PUSH (Word (Val "0")); SUB; PUSH (Word (Val "3")); ADD;] in
        let tp =  [PUSH (Word (Val "4")); SUB] in
        let ea = Enc_consts.mk sp `All in
        let c = enc_trans_val ea tp in
        assert_bool "no model found" (is_sat [c])
      );

    "show equivalence with long source program" >::(fun _ ->
        let sp =
          [PUSH (Word (Val "0")); DUP I; PUSH (Word (Val "0")); DUP I; PUSH (Word (Val "0"));
           PUSH (Word (Val "0")); PUSH (Word (Val "0")); ADD; ADD; ADD; ADD; ADD; ADD; DUP II]
        in
        let tp =  [PUSH (Word (Val "0")); DUP II] in
        let ea = Enc_consts.mk sp `All in
        let c = enc_trans_val ea tp in
        assert_bool "not unsat" (is_unsat [c])
      );

    "disprove equivalence that would be valid with 2 bit words" >::(fun _ ->
        let sp = [PUSH (Word (Val "0")); SUB; PUSH (Word (Val "3")); ADD;] in
        let tp =  [NOT] in
        let ea = Enc_consts.mk sp `All in
        let c = enc_trans_val ea tp in
        assert_bool "no model found" (is_sat [c])
      );

    "disprove equivalence that holds for 4 bit" >::(fun _ ->
        let sp = [PUSH (Word (Val "15")); NOT; ADD] in
        let tp = [] in
        let ea = Enc_consts.mk sp `All in
        let c = enc_trans_val ea tp in
        assert_bool "no model found" (is_sat [c])
      );

    "validation with uninterpreted instruction" >::(fun _ ->
        let sp = [PC; PUSH (Word (Val "0")); ADD;] in
        let tp = [PC] in
        let ea = Enc_consts.mk sp `All in
        let c = enc_trans_val ea tp in
        assert_bool "not unsat" (is_unsat [c])
      );

    "validation with storage: sload from same key twice" >:: (fun _ ->
        let key = Pusharg.Word (Val "1") in
        let sp = [PUSH key; SLOAD; PUSH key; SLOAD] in
        let tp = [PUSH key; SLOAD; DUP I] in
        let ea = Enc_consts.mk sp `All in
        let c = enc_trans_val ea tp in
        assert_bool "not unsat" (is_unsat [c])
      );

    "validation with storage: overwrite sstored value" >:: (fun _ ->
        let value1 = Pusharg.Word (Val "1") and value2 = Pusharg.Word (Val "2") in
        let key = Pusharg.Word (Val "3") in
        let sp = [PUSH value1; PUSH key; SSTORE; PUSH value2; PUSH key; SSTORE] in
        let tp = [PUSH value2; PUSH key; SSTORE] in
        let ea = Enc_consts.mk sp `All in
        let c = enc_trans_val ea tp in
        assert_bool "not unsat" (is_unsat [c])
      );
  ]

let () =
  run_test_tt_main suite
