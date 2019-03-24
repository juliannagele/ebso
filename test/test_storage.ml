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

let gas_cost =
  [
    "cost of a single SSTORE with value 0, no refund" >:: (fun _ ->
        let k = Stackarg.Val "1" in
        let p = [PUSH (Val "0"); PUSH k; SSTORE] in
        let ea = mk_enc_consts p (`User []) in
        let st = mk_state ea "" in
        let c = foralls (forall_vars ea) (enc_program ea st) in
        let m = solve_model_exn [c] in
        let xsstore0 = senum 0 in
        assert_equal ~cmp:[%eq: int] ~printer:Int.to_string
          5006
          (eval_gas ~xs:[xsstore0] st m (List.length p))
      );

    "cost of a single SSTORE with value 0, with refund" >:: (fun _ ->
        let k = Stackarg.Val "1" in
        let p = [PUSH (Val "0"); PUSH k; SSTORE] in
        let ea = mk_enc_consts p (`User []) in
        let st = mk_state ea "" in
        let c = foralls (forall_vars ea) (enc_program ea st) in
        let m = solve_model_exn [c] in
        let xsstore0 = senum 2 in
        assert_equal ~cmp:[%eq: int] ~printer:Int.to_string
          (-9994)
          (eval_gas ~xs:[xsstore0] st m (List.length p))
      );

    "cost of a single SSTORE with non-zero value, overwriting zero" >:: (fun _ ->
        let k = Stackarg.Val "1" in
        let p = [PUSH (Val "2"); PUSH k; SSTORE] in
        let ea = mk_enc_consts p (`User []) in
        let st = mk_state ea "" in
        let c = foralls (forall_vars ea) (enc_program ea st) in
        let m = solve_model_exn [c] in
        let xsstore0 = senum 0 in
        assert_equal ~cmp:[%eq: int] ~printer:Int.to_string
          20006
          (eval_gas ~xs:[xsstore0] st m (List.length p))
      );

    "cost of a single SSTORE with non-zero value, overwriting non-zero" >:: (fun _ ->
        let k = Stackarg.Val "1" in
        let p = [PUSH (Val "3"); PUSH k; SSTORE] in
        let ea = mk_enc_consts p (`User []) in
        let st = mk_state ea "" in
        let c = foralls (forall_vars ea) (enc_program ea st) in
        let m = solve_model_exn [c] in
        let xsstore0 = senum 2 in
        assert_equal ~cmp:[%eq: int] ~printer:Int.to_string
          5006
          (eval_gas ~xs:[xsstore0] st m (List.length p))
      );

    "cost of SSTORing 0 to same key twice, no refund" >:: (fun _ ->
        let k = Stackarg.Val "1" in
        let p = [PUSH (Val "0"); PUSH k; SSTORE; PUSH (Val "0"); PUSH k; SSTORE] in
        let ea = mk_enc_consts p (`User []) in
        let st = mk_state ea "" in
        let c = foralls (forall_vars ea) (enc_program ea st) in
        let m = solve_model_exn [c] in
        let xsstore0 = senum 0 in
        assert_equal ~cmp:[%eq: int] ~printer:Int.to_string
          10012
          (eval_gas ~xs:[xsstore0; xsstore0] st m (List.length p))
      );

    "cost of SSTORing 0 to same key twice, with refund" >:: (fun _ ->
        let k = Stackarg.Val "1" in
        let p = [PUSH (Val "0"); PUSH k; SSTORE; PUSH (Val "0"); PUSH k; SSTORE] in
        let ea = mk_enc_consts p (`User []) in
        let st = mk_state ea "" in
        let c = foralls (forall_vars ea) (enc_program ea st) in
        let m = solve_model_exn [c] in
        let xsstore0 = senum 2 in
        assert_equal ~cmp:[%eq: int] ~printer:Int.to_string
          (-4988)
          (eval_gas ~xs:[xsstore0; xsstore0] st m (List.length p))
      );

    "cost of SSTORing 0 then non-zero to same key, no refund" >:: (fun _ ->
        let k = Stackarg.Val "1" in
        let p = [PUSH (Val "0"); PUSH k; SSTORE; PUSH (Val "2"); PUSH k; SSTORE] in
        let ea = mk_enc_consts p (`User []) in
        let st = mk_state ea "" in
        let c = foralls (forall_vars ea) (enc_program ea st) in
        let m = solve_model_exn [c] in
        let xsstore0 = senum 0 in
        assert_equal ~cmp:[%eq: int] ~printer:Int.to_string
          25012
          (eval_gas ~xs:[xsstore0; xsstore0] st m (List.length p))
      );

    "cost of SSTORing 0 then non-zero to same key, with refund" >:: (fun _ ->
        let k = Stackarg.Val "1" in
        let p = [PUSH (Val "0"); PUSH k; SSTORE; PUSH (Val "2"); PUSH k; SSTORE] in
        let ea = mk_enc_consts p (`User []) in
        let st = mk_state ea "" in
        let c = foralls (forall_vars ea) (enc_program ea st) in
        let m = solve_model_exn [c] in
        let xsstore0 = senum 2 in
        assert_equal ~cmp:[%eq: int] ~printer:Int.to_string
          10012
          (eval_gas ~xs:[xsstore0; xsstore0] st m (List.length p))
      );

    "cost of SSTORing non-zero then zero to same key, overwriting zero" >:: (fun _ ->
        let k = Stackarg.Val "1" in
        let p = [PUSH (Val "2"); PUSH k; SSTORE; PUSH (Val "0"); PUSH k; SSTORE] in
        let ea = mk_enc_consts p (`User []) in
        let st = mk_state ea "" in
        let c = foralls (forall_vars ea) (enc_program ea st) in
        let m = solve_model_exn [c] in
        let xsstore0 = senum 0 in
        assert_equal ~cmp:[%eq: int] ~printer:Int.to_string
          10012
          (eval_gas ~xs:[xsstore0; xsstore0] st m (List.length p))
      );

    "cost of SSTORing non-zero then zero to same key, overwriting non-zero" >:: (fun _ ->
        let k = Stackarg.Val "1" in
        let p = [PUSH (Val "2"); PUSH k; SSTORE; PUSH (Val "0"); PUSH k; SSTORE] in
        let ea = mk_enc_consts p (`User []) in
        let st = mk_state ea "" in
        let c = foralls (forall_vars ea) (enc_program ea st) in
        let m = solve_model_exn [c] in
        let xsstore0 = senum 2 in
        assert_equal ~cmp:[%eq: int] ~printer:Int.to_string
          (-4988)
          (eval_gas ~xs:[xsstore0; xsstore0] st m (List.length p))
      );

    "cost of SSTORing non-zero to same key twice, overwriting zero" >:: (fun _ ->
        let k = Stackarg.Val "1" in
        let p = [PUSH (Val "2"); PUSH k; SSTORE; PUSH (Val "3"); PUSH k; SSTORE] in
        let ea = mk_enc_consts p (`User []) in
        let st = mk_state ea "" in
        let c = foralls (forall_vars ea) (enc_program ea st) in
        let m = solve_model_exn [c] in
        let xsstore0 = senum 0 in
        assert_equal ~cmp:[%eq: int] ~printer:Int.to_string
          25012
          (eval_gas ~xs:[xsstore0; xsstore0] st m (List.length p))
      );

    "cost of SSTORing non-zero to same key twice, overwriting non-zero" >:: (fun _ ->
        let k = Stackarg.Val "1" in
        let p = [PUSH (Val "2"); PUSH k; SSTORE; PUSH (Val "3"); PUSH k; SSTORE] in
        let ea = mk_enc_consts p (`User []) in
        let st = mk_state ea "" in
        let c = foralls (forall_vars ea) (enc_program ea st) in
        let m = solve_model_exn [c] in
        let xsstore0 = senum 2 in
        assert_equal ~cmp:[%eq: int] ~printer:Int.to_string
          10012
          (eval_gas ~xs:[xsstore0; xsstore0] st m (List.length p))
      );
  ]

let effect = []

let suite =
  (* set low for fast testing *)
  set_wsz 3; set_sas 6;
  "suite" >:::
  effect @ gas_cost

let () =
  run_test_tt_main suite
