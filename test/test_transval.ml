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
open Core
open OUnit2
open Z3util
open Instruction
open Evmenc

let suite =
  (* set to realistic values for validation *)
  set_wsz 256; set_sas 10;
  "suite" >:::
  [
    (* translation validation *)

    "show equivalence of 3 + (0 - x) and (3 - x)" >::(fun _ ->
        let sp = [PUSH (Val "0"); SUB; PUSH (Val "3"); ADD;] in
        let tp =  [PUSH (Val "3"); SUB] in
        let ea = mk_enc_consts sp `All in
        let c = enc_trans_val ea tp in
        let m = solve_model [c] in
        assert_bool "not unsat" (Option.is_none m)
      );

    "show difference of 3 + (0 - x) and (4 - x)" >::(fun _ ->
        let sp = [PUSH (Val "0"); SUB; PUSH (Val "3"); ADD;] in
        let tp =  [PUSH (Val "4"); SUB] in
        let ea = mk_enc_consts sp `All in
        let c = enc_trans_val ea tp in
        let m = solve_model [c] in
        assert_bool "no model found" (Option.is_some m)
      );

    "show equivalence with long source program" >::(fun _ ->
        let sp =
          [PUSH (Val "0"); DUP I; PUSH (Val "0"); DUP I; PUSH (Val "0");
           PUSH (Val "0"); PUSH (Val "0"); ADD; ADD; ADD; ADD; ADD; ADD; DUP II]
        in
        let tp =  [PUSH (Val "0"); DUP II] in
        let ea = mk_enc_consts sp `All in
        let c = enc_trans_val ea tp in
        let m = solve_model [c] in
        assert_bool "not unsat" (Option.is_none m)
      );

    "disprove equivalence that would be valid with 2 bit words" >::(fun _ ->
        let sp = [PUSH (Val "0"); SUB; PUSH (Val "3"); ADD;] in
        let tp =  [NOT] in
        let ea = mk_enc_consts sp `All in
        let c = enc_trans_val ea tp in
        let m = solve_model [c] in
        assert_bool "no model found" (Option.is_some m)
      );

    "disprove equivalence that holds for 4 bit" >::(fun _ ->
        let sp = [PUSH (Val "15"); NOT; ADD] in
        let tp = [] in
        let ea = mk_enc_consts sp `All in
        let c = enc_trans_val ea tp in
        let m = solve_model [c] in
        assert_bool "no model found" (Option.is_some m)
      );

    "validation with uninterpreted instruction" >::(fun _ ->
        let sp = [PC; PUSH (Val "0"); ADD;] in
        let tp = [PC] in
        let ea = mk_enc_consts sp `All in
        let c = enc_trans_val ea tp in
        let m = solve_model [c] in
        assert_bool "not unsat" (Option.is_none m)
      );

  ]

let () =
  run_test_tt_main suite
