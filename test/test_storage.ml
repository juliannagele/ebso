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

let effect =
  [
    "Non-accessed keys evaluate to default value" >:: (fun _ ->
        let p = [PUSH (Val "1"); PUSH (Val "2"); SSTORE] in
        let ea = mk_enc_consts p (`User []) in
        let st = mk_state ea "" in
        let c = foralls (forall_vars ea) (enc_program ea st) in
        let m = solve_model_exn [c] in
        let keys = [senum 0; senum 1] in
        let xsstore0 = senum 3 in
        assert_equal
          ~cmp:[%eq: Z3.Expr.t list] ~printer:(List.to_string ~f:Z3.Expr.to_string)
          [senum 0; senum 0]
          (List.map keys ~f:(eval_storage ~xs:[xsstore0] st m 0))
      );

    "No SLOAD, return variable for key of SSTORE" >:: (fun _ ->
        let p = [PUSH (Val "1"); PUSH (Val "2"); SSTORE] in
        let ea = mk_enc_consts p (`User []) in
        let st = mk_state ea "" in
        let c = foralls (forall_vars ea) (enc_program ea st) in
        let m = solve_model_exn [c] in
        let xsstore0 = senum 3 in (* initialize universally quantified variable to 3 *)
        assert_equal
          ~cmp:[%eq: Z3.Expr.t] ~printer:Z3.Expr.to_string
          xsstore0
          (eval_storage ~xs:[xsstore0] st m 0 (senum 2))
      );

    "SLOAD a key" >:: (fun _ ->
        let k = Stackarg.Val "1" in
        let p = [PUSH k; SLOAD] in
        let ea = mk_enc_consts p (`User []) in
        let st = mk_state ea "" in
        let c = foralls (forall_vars ea) (enc_program ea st) in
        let m = solve_model_exn [c] in
        let xsload0 = senum 3 in (* set for all quantified variable to 3 for test *)
        assert_equal ~cmp:[%eq: Z3.Expr.t] ~printer:Z3.Expr.to_string
          xsload0
          (eval_storage ~xs:[xsload0] st m 0 (enc_stackarg ea (num 0) k))
      );

    "SLOAD a key not in range" >:: (fun _ ->
        let k1 = Stackarg.Val "1" in
        let k2 = Stackarg.Val "2" in
        let p = [PUSH k1; SLOAD] in
        let ea = mk_enc_consts p (`User []) in
        let st = mk_state ea "" in
        let c = foralls (forall_vars ea) (enc_program ea st) in
        let m = solve_model_exn [c] in
        let xsload0 = senum 3 in (* set for all quantified variable to 3 for test *)
        assert_equal ~cmp:[%eq: Z3.Expr.t] ~printer:Z3.Expr.to_string
          (senum 0)
          (eval_storage ~xs:[xsload0] st m 0 (enc_stackarg ea (num 0) k2))
      );

    "SLOAD twice from same key" >:: (fun _ ->
        let k = Stackarg.Val "1" in
        let p = [PUSH k; SLOAD; PUSH k; SLOAD] in
        let ea = mk_enc_consts p (`User []) in
        let st = mk_state ea "" in
        let c = foralls (forall_vars ea) (enc_program ea st) in
        let m = solve_model_exn [c] in
        let xsload0 = senum 3 and xsload1 = senum 2 in
        assert_equal ~cmp:[%eq: Z3.Expr.t] ~printer:Z3.Expr.to_string
          xsload0
          (eval_storage ~xs:[xsload0; xsload1] st m 0 (enc_stackarg ea (num 0) k))
      );

    "SLOAD twice from different key" >:: (fun _ ->
        let k1 = Stackarg.Val "1" and k2 = Stackarg.Val "2" in
        let p = [PUSH k1; SLOAD; PUSH k2; SLOAD] in
        let ea = mk_enc_consts p (`User []) in
        let st = mk_state ea "" in
        let c = foralls (forall_vars ea) (enc_program ea st) in
        let m = solve_model_exn [c] in
        let xsload0 = senum 3 and xsload1 = senum 2 in
        assert_equal ~cmp:[%eq: Z3.Expr.t list]
          ~printer:(List.to_string ~f:Z3.Expr.to_string)
          [xsload0; xsload1]
          [(eval_storage ~xs:[xsload0; xsload1] st m 0 (enc_stackarg ea (num 0) k1));
           (eval_storage ~xs:[xsload0; xsload1] st m 0 (enc_stackarg ea (num 0) k2))]
      );

    "SLOAD from key after SSTORE" >:: (fun _ ->
        let k = Stackarg.Val "1" in
        let v = Stackarg.Val "2" in
        let p = [PUSH v; PUSH k; SSTORE; PUSH k; SLOAD] in
        let ea = mk_enc_consts p (`User []) in
        let st = mk_state ea "" in
        let c = foralls (forall_vars ea) (enc_program ea st) in
        let m = solve_model_exn [c] in
        let xsload0 = senum 3 and xsstore0 = senum 4 in
        (* storage is initalized with xsload0, because SLOAD variables
           are ordered before SSTORE variables *)
        assert_equal ~cmp:[%eq: Z3.Expr.t] ~printer:Z3.Expr.to_string
          xsload0
          (eval_storage ~xs:[xsload0; xsstore0] st m 0 (enc_stackarg ea (num 0) k))
      );

    "SLOAD twice from same key with SSTORE in between" >:: (fun _ ->
        let k = Stackarg.Val "1" in
        let v = Stackarg.Val "2" in
        let p = [PUSH k; SLOAD; PUSH v; PUSH k; SSTORE; PUSH k; SLOAD] in
        let ea = mk_enc_consts p (`User []) in
        let st = mk_state ea "" in
        let c = foralls (forall_vars ea) (enc_program ea st) in
        let m = solve_model_exn [c] in
        let xsload0 = senum 3 and xsload1 = senum 2 and xsstore0 = senum 4 in
        assert_equal ~cmp:[%eq: Z3.Expr.t] ~printer:Z3.Expr.to_string
          xsload0
          (eval_storage ~xs:[xsload0; xsload1; xsstore0] st m 0 (enc_stackarg ea (num 0) k))
      );

    "SLOAD SSTOREd value" >:: (fun _ ->
        let k = Stackarg.Val "1" in
        let v = Stackarg.Val "2" in
        let p = [PUSH k; SLOAD; PUSH v; PUSH k; SSTORE; PUSH k; SLOAD] in
        let ea = mk_enc_consts p (`User []) in
        let st = mk_state ea "" in
        let c = foralls (forall_vars ea) (enc_program ea st) in
        let m = solve_model_exn [c] in
        let xsload0 = senum 3 and xsload1 = senum 2 and xsstore0 = senum 4 in
        assert_equal ~cmp:[%eq: Z3.Expr.t] ~printer:Z3.Expr.to_string
          (senum 2)
          (eval_storage ~xs:[xsload0; xsload1; xsstore0] st m (List.length p) (enc_stackarg ea (num 0) k))
      );

    "SSTORE twice to same key" >:: (fun _ ->
        let k = Stackarg.Val "1" in
        let v1 = Stackarg.Val "2" and v2 = Stackarg.Val "3" in
        let p1 = [PUSH v1; PUSH k; SSTORE] and p2 = [PUSH v2; PUSH k; SSTORE] in
        let p = p1 @ p2 in
        let ea = mk_enc_consts p (`User []) in
        let st = mk_state ea "" in
        let c = foralls (forall_vars ea) (enc_program ea st) in
        let m = solve_model_exn [c] in
        let xsstore0 = senum 1 and xsstore1 = senum 4 in
        assert_equal ~cmp:[%eq: Z3.Expr.t list] ~printer:(List.to_string ~f:Z3.Expr.to_string)
          [(senum 2); (senum 3)]
          [(eval_storage ~xs:[xsstore0; xsstore1] st m (List.length p1) (enc_stackarg ea (num 0) k));
           (eval_storage ~xs:[xsstore0; xsstore1] st m (List.length p) (enc_stackarg ea (num 0) k))]
      );
  ]

let suite =
  (* set low for fast testing *)
  set_wsz 3; set_sas 6;
  "suite" >:::
  effect @ gas_cost

let () =
  run_test_tt_main suite
