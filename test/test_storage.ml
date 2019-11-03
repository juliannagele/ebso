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
open Ebso
open Z3util
open Instruction
open Evmenc
open Pusharg
open Enc_consts

let gas_cost =
  [
    "cost of a single SSTORE with value 0, no refund" >:: (fun _ ->
        let k = Word (Val "1") in
        let p = [PUSH (Word (Val "0")); PUSH k; SSTORE] in
        let ea = Enc_consts.mk p (`User []) in
        let st = mk_state ea "" in
        let c = foralls (forall_vars ea) (enc_program ea st) in
        let m = solve_model_exn [c] in
        let xsstore0 = Word.enc_int 0 in
        assert_equal ~cmp:[%eq: GC.t] ~printer:[%show: GC.t]
          (GC.of_int 5006)
          (eval_gas ~xs:[xsstore0] st m (Program.length p))
      );

    "cost of a single SSTORE with value 0, with refund" >:: (fun _ ->
        let k = Word (Val "1") in
        let p = [PUSH (Word (Val "0")); PUSH k; SSTORE] in
        let ea = Enc_consts.mk p (`User []) in
        let st = mk_state ea "" in
        let c = foralls (forall_vars ea) (enc_program ea st) in
        let m = solve_model_exn [c] in
        let xsstore0 = Word.enc_int 2 in
        assert_equal ~cmp:[%eq: GC.t] ~printer:[%show: GC.t]
          (GC.of_int (-9994))
          (eval_gas ~xs:[xsstore0] st m (Program.length p))
      );

    "cost of a single SSTORE with non-zero value, overwriting zero" >:: (fun _ ->
        let k = Word (Val "1") in
        let p = [PUSH (Word (Val "2")); PUSH k; SSTORE] in
        let ea = Enc_consts.mk p (`User []) in
        let st = mk_state ea "" in
        let c = foralls (forall_vars ea) (enc_program ea st) in
        let m = solve_model_exn [c] in
        let xsstore0 = Word.enc_int 0 in
        assert_equal ~cmp:[%eq: GC.t] ~printer:[%show: GC.t]
          (GC.of_int 20006)
          (eval_gas ~xs:[xsstore0] st m (Program.length p))
      );

    "cost of a single SSTORE with non-zero value, overwriting non-zero" >:: (fun _ ->
        let k = Word (Val "1") in
        let p = [PUSH (Word (Val "3")); PUSH k; SSTORE] in
        let ea = Enc_consts.mk p (`User []) in
        let st = mk_state ea "" in
        let c = foralls (forall_vars ea) (enc_program ea st) in
        let m = solve_model_exn [c] in
        let xsstore0 = Word.enc_int 2 in
        assert_equal ~cmp:[%eq: GC.t] ~printer:[%show: GC.t]
          (GC.of_int 5006)
          (eval_gas ~xs:[xsstore0] st m (Program.length p))
      );

    "cost of SSTORing 0 to same key twice, no refund" >:: (fun _ ->
        let k = Word (Val "1") in
        let p = [PUSH (Word (Val "0")); PUSH k; SSTORE; PUSH (Word (Val "0")); PUSH k; SSTORE] in
        let ea = Enc_consts.mk p (`User []) in
        let st = mk_state ea "" in
        let c = foralls (forall_vars ea) (enc_program ea st) in
        let m = solve_model_exn [c] in
        let xsstore0 = Word.enc_int 0 in
        assert_equal ~cmp:[%eq: GC.t] ~printer:[%show: GC.t]
          (GC.of_int 10012)
          (eval_gas ~xs:[xsstore0; xsstore0] st m (Program.length p))
      );

    "cost of SSTORing 0 to same key twice, with refund" >:: (fun _ ->
        let k = Word (Val "1") in
        let p = [PUSH (Word (Val "0")); PUSH k; SSTORE; PUSH (Word (Val "0")); PUSH k; SSTORE] in
        let ea = Enc_consts.mk p (`User []) in
        let st = mk_state ea "" in
        let c = foralls (forall_vars ea) (enc_program ea st) in
        let m = solve_model_exn [c] in
        let xsstore0 = Word.enc_int 2 in
        assert_equal ~cmp:[%eq: GC.t] ~printer:[%show: GC.t]
          (GC.of_int (-4988))
          (eval_gas ~xs:[xsstore0; xsstore0] st m (Program.length p))
      );

    "cost of SSTORing 0 then non-zero to same key, no refund" >:: (fun _ ->
        let k = Word (Val "1") in
        let p = [PUSH (Word (Val "0")); PUSH k; SSTORE; PUSH (Word (Val "2")); PUSH k; SSTORE] in
        let ea = Enc_consts.mk p (`User []) in
        let st = mk_state ea "" in
        let c = foralls (forall_vars ea) (enc_program ea st) in
        let m = solve_model_exn [c] in
        let xsstore0 = Word.enc_int 0 in
        assert_equal ~cmp:[%eq: GC.t] ~printer:[%show: GC.t]
          (GC.of_int 25012)
          (eval_gas ~xs:[xsstore0; xsstore0] st m (Program.length p))
      );

    "cost of SSTORing 0 then non-zero to same key, with refund" >:: (fun _ ->
        let k = Word (Val "1") in
        let p = [PUSH (Word (Val "0")); PUSH k; SSTORE; PUSH (Word (Val "2")); PUSH k; SSTORE] in
        let ea = Enc_consts.mk p (`User []) in
        let st = mk_state ea "" in
        let c = foralls (forall_vars ea) (enc_program ea st) in
        let m = solve_model_exn [c] in
        let xsstore0 = Word.enc_int 2 in
        assert_equal ~cmp:[%eq: GC.t] ~printer:[%show: GC.t]
          (GC.of_int 10012)
          (eval_gas ~xs:[xsstore0; xsstore0] st m (Program.length p))
      );

    "cost of SSTORing non-zero then zero to same key, overwriting zero" >:: (fun _ ->
        let k = Word (Val "1") in
        let p = [PUSH (Word (Val "2")); PUSH k; SSTORE; PUSH (Word (Val "0")); PUSH k; SSTORE] in
        let ea = Enc_consts.mk p (`User []) in
        let st = mk_state ea "" in
        let c = foralls (forall_vars ea) (enc_program ea st) in
        let m = solve_model_exn [c] in
        let xsstore0 = Word.enc_int 0 in
        assert_equal ~cmp:[%eq: GC.t] ~printer:[%show: GC.t]
          (GC.of_int 10012)
          (eval_gas ~xs:[xsstore0; xsstore0] st m (Program.length p))
      );

    "cost of SSTORing non-zero then zero to same key, overwriting non-zero" >:: (fun _ ->
        let k = Word (Val "1") in
        let p = [PUSH (Word (Val "2")); PUSH k; SSTORE; PUSH (Word (Val "0")); PUSH k; SSTORE] in
        let ea = Enc_consts.mk p (`User []) in
        let st = mk_state ea "" in
        let c = foralls (forall_vars ea) (enc_program ea st) in
        let m = solve_model_exn [c] in
        let xsstore0 = Word.enc_int 2 in
        assert_equal ~cmp:[%eq: GC.t] ~printer:[%show: GC.t]
          (GC.of_int (-4988))
          (eval_gas ~xs:[xsstore0; xsstore0] st m (Program.length p))
      );

    "cost of SSTORing non-zero to same key twice, overwriting zero" >:: (fun _ ->
        let k = Word (Val "1") in
        let p = [PUSH (Word (Val "2")); PUSH k; SSTORE; PUSH (Word (Val "3")); PUSH k; SSTORE] in
        let ea = Enc_consts.mk p (`User []) in
        let st = mk_state ea "" in
        let c = foralls (forall_vars ea) (enc_program ea st) in
        let m = solve_model_exn [c] in
        let xsstore0 = Word.enc_int 0 in
        assert_equal ~cmp:[%eq: GC.t] ~printer:[%show: GC.t]
          (GC.of_int 25012)
          (eval_gas ~xs:[xsstore0; xsstore0] st m (Program.length p))
      );

    "cost of SSTORing non-zero to same key twice, overwriting non-zero" >:: (fun _ ->
        let k = Word (Val "1") in
        let p = [PUSH (Word (Val "2")); PUSH k; SSTORE; PUSH (Word (Val "3")); PUSH k; SSTORE] in
        let ea = Enc_consts.mk p (`User []) in
        let st = mk_state ea "" in
        let c = foralls (forall_vars ea) (enc_program ea st) in
        let m = solve_model_exn [c] in
        let xsstore0 = Word.enc_int 2 in
        assert_equal ~cmp:[%eq: GC.t] ~printer:[%show: GC.t]
          (GC.of_int 10012)
          (eval_gas ~xs:[xsstore0; xsstore0] st m (Program.length p))
      );

    "cost of SSTOREing an input value" >:: (fun _ ->
        let p = [PUSH (Word (Val "9")); SSTORE] in
        let ea = Enc_consts.mk p (`User []) in
        let st = mk_state ea "" in
        let c = foralls (forall_vars ea) (enc_program ea st) in
        let m = solve_model_exn [c] in
        let xs0 = Word.enc_int 1 and xsstore0 = Word.enc_int 1 in
        assert_equal ~cmp:[%eq: GC.t] ~printer:[%show: GC.t]
          (GC.of_int 5003)
          (eval_gas ~xs:[xs0; xsstore0] st m (Program.length p))
      );

    "cost of SSTOREing an input value with stack operations between" >:: (fun _ ->
        let p = [PUSH (Word (Val "9")); DUP II; SWAP I; SSTORE; POP] in
        let ea = Enc_consts.mk p (`User []) in
        let st = mk_state ea "" in
        let c = foralls (forall_vars ea) (enc_program ea st) in
        let m = solve_model_exn [c] in
        let xs0 = Word.enc_int 1 and xsstore0 = Word.enc_int 1 in
        assert_equal ~cmp:[%eq: GC.t] ~printer:[%show: GC.t]
          (GC.of_int 5011)
          (eval_gas ~xs:[xs0; xsstore0] st m (Program.length p))
      );

  ]

let effect =
  [
    "Non-accessed keys evaluate to default value" >:: (fun _ ->
        let p = [PUSH (Word (Val "1")); PUSH (Word (Val "2")); SSTORE] in
        let ea = Enc_consts.mk p (`User []) in
        let st = mk_state ea "" in
        let c = foralls (forall_vars ea) (enc_program ea st) in
        let m = solve_model_exn [c] in
        let keys = [Word.enc_int 0; Word.enc_int 1] in
        let xsstore0 = Word.enc_int 3 in
        assert_equal
          ~cmp:[%eq: Z3.Expr.t list] ~printer:(List.to_string ~f:Z3.Expr.to_string)
          [Word.enc_int 0; Word.enc_int 0]
          (List.map keys ~f:(eval_storage ~xs:[xsstore0] st m (PC.of_int 0)))
      );

    "No SLOAD, return variable for key of SSTORE" >:: (fun _ ->
        let p = [PUSH (Word (Val "1")); PUSH (Word (Val "2")); SSTORE] in
        let ea = Enc_consts.mk p (`User []) in
        let st = mk_state ea "" in
        let c = foralls (forall_vars ea) (enc_program ea st) in
        let m = solve_model_exn [c] in
        let xsstore0 = Word.enc_int 3 in (* initialize universally quantified variable to 3 *)
        assert_equal
          ~cmp:[%eq: Z3.Expr.t] ~printer:Z3.Expr.to_string
          xsstore0
          (eval_storage ~xs:[xsstore0] st m (PC.of_int 0) (Word.enc_int 2))
      );

    "SLOAD a key" >:: (fun _ ->
        let k = Word (Val "1") in
        let p = [PUSH k; SLOAD] in
        let ea = Enc_consts.mk p (`User []) in
        let st = mk_state ea "" in
        let c = foralls (forall_vars ea) (enc_program ea st) in
        let m = solve_model_exn [c] in
        let xsload0 = Word.enc_int 3 in (* set for all quantified variable to 3 for test *)
        assert_equal ~cmp:[%eq: Z3.Expr.t] ~printer:Z3.Expr.to_string
          xsload0
          (eval_storage ~xs:[xsload0] st m (PC.of_int 0) (Pusharg.enc ea.a (num 0) k))
      );

    "SLOAD a key not in range" >:: (fun _ ->
        let k1 = Word (Val "1") in
        let k2 = Word (Val "2") in
        let p = [PUSH k1; SLOAD] in
        let ea = Enc_consts.mk p (`User []) in
        let st = mk_state ea "" in
        let c = foralls (forall_vars ea) (enc_program ea st) in
        let m = solve_model_exn [c] in
        let xsload0 = Word.enc_int 3 in (* set for all quantified variable to 3 for test *)
        assert_equal ~cmp:[%eq: Z3.Expr.t] ~printer:Z3.Expr.to_string
          (Word.enc_int 0)
          (eval_storage ~xs:[xsload0] st m (PC.of_int 0) (Pusharg.enc ea.a (num 0) k2))
      );

    "SLOAD twice from same key" >:: (fun _ ->
        let k = Word (Val "1") in
        let p = [PUSH k; SLOAD; PUSH k; SLOAD] in
        let ea = Enc_consts.mk p (`User []) in
        let st = mk_state ea "" in
        let c = foralls (forall_vars ea) (enc_program ea st) in
        let m = solve_model_exn [c] in
        let xsload0 = Word.enc_int 3 and xsload1 = Word.enc_int 2 in
        assert_equal ~cmp:[%eq: Z3.Expr.t] ~printer:Z3.Expr.to_string
          xsload0
          (eval_storage ~xs:[xsload0; xsload1] st m (PC.of_int 0) (Pusharg.enc ea.a (num 0) k))
      );

    "SLOAD twice from different key" >:: (fun _ ->
        let k1 = Word (Val "1") and k2 = Word (Val "2") in
        let p = [PUSH k1; SLOAD; PUSH k2; SLOAD] in
        let ea = Enc_consts.mk p (`User []) in
        let st = mk_state ea "" in
        let c = foralls (forall_vars ea) (enc_program ea st) in
        let m = solve_model_exn [c] in
        let xsload0 = Word.enc_int 3 and xsload1 = Word.enc_int 2 in
        assert_equal ~cmp:[%eq: Z3.Expr.t list]
          ~printer:(List.to_string ~f:Z3.Expr.to_string)
          [xsload0; xsload1]
          [(eval_storage ~xs:[xsload0; xsload1] st m (PC.of_int 0) (Pusharg.enc ea.a (num 0) k1));
           (eval_storage ~xs:[xsload0; xsload1] st m (PC.of_int 0) (Pusharg.enc ea.a (num 0) k2))]
      );

    "SLOAD from key after SSTORE" >:: (fun _ ->
        let k = Word (Val "1") in
        let v = Word (Val "2") in
        let p = [PUSH v; PUSH k; SSTORE; PUSH k; SLOAD] in
        let ea = Enc_consts.mk p (`User []) in
        let st = mk_state ea "" in
        let c = foralls (forall_vars ea) (enc_program ea st) in
        let m = solve_model_exn [c] in
        let xsload0 = Word.enc_int 3 and xsstore0 = Word.enc_int 4 in
        (* storage is initalized with xsload0, because SLOAD variables
           are ordered before SSTORE variables *)
        assert_equal ~cmp:[%eq: Z3.Expr.t] ~printer:Z3.Expr.to_string
          xsload0
          (eval_storage ~xs:[xsload0; xsstore0] st m (PC.of_int 0) (Pusharg.enc ea.a (num 0) k))
      );

    "SLOAD twice from same key with SSTORE in between" >:: (fun _ ->
        let k = Word (Val "1") in
        let v = Word (Val "2") in
        let p = [PUSH k; SLOAD; PUSH v; PUSH k; SSTORE; PUSH k; SLOAD] in
        let ea = Enc_consts.mk p (`User []) in
        let st = mk_state ea "" in
        let c = foralls (forall_vars ea) (enc_program ea st) in
        let m = solve_model_exn [c] in
        let xsload0 = Word.enc_int 3 and xsload1 = Word.enc_int 2 and xsstore0 = Word.enc_int 4 in
        assert_equal ~cmp:[%eq: Z3.Expr.t] ~printer:Z3.Expr.to_string
          xsload0
          (eval_storage ~xs:[xsload0; xsload1; xsstore0] st m (PC.of_int 0) (Pusharg.enc ea.a (num 0) k))
      );

    "SLOAD SSTOREd value" >:: (fun _ ->
        let k = Word (Val "1") in
        let v = Word (Val "2") in
        let p = [PUSH k; SLOAD; PUSH v; PUSH k; SSTORE; PUSH k; SLOAD] in
        let ea = Enc_consts.mk p (`User []) in
        let st = mk_state ea "" in
        let c = foralls (forall_vars ea) (enc_program ea st) in
        let m = solve_model_exn [c] in
        let xsload0 = Word.enc_int 3 and xsload1 = Word.enc_int 2 and xsstore0 = Word.enc_int 4 in
        assert_equal ~cmp:[%eq: Z3.Expr.t] ~printer:Z3.Expr.to_string
          (Word.enc_int 2)
          (eval_storage ~xs:[xsload0; xsload1; xsstore0] st m (Program.length p) (Pusharg.enc ea.a (num 0) k))
      );

    "SSTORE to SLOADed key" >: test_case ~length:Long (fun _ ->
        let k1 = Word (Val "1") and k2 = Word (Val "3") in
        let v = Word (Val "4") in
        let p = [PUSH k1; SLOAD; PUSH v; PUSH k1; SSTORE; PUSH k2; SLOAD] in
        let ea = Enc_consts.mk p (`User []) in
        let st = mk_state ea "" in
        let c = foralls (forall_vars ea) (enc_program ea st) in
        let m = solve_model_exn [c] in
        let xsload0 = Word.enc_int 3 and xsload1 = Word.enc_int 2 and xsstore0 = Word.enc_int 5 in
        assert_equal ~cmp:[%eq: Z3.Expr.t list] ~printer:(List.to_string ~f:Z3.Expr.to_string)
          [(Word.enc_int 4); (Word.enc_int 2)]
          [(eval_storage ~xs:[xsload0; xsload1; xsstore0] st m (Program.length p) (Pusharg.enc ea.a (num 0) k1));
           (eval_storage ~xs:[xsload0; xsload1; xsstore0] st m (Program.length p) (Pusharg.enc ea.a (num 0) k2))]
      );

    "SSTORE twice to same key" >:: (fun _ ->
        let k = Word (Val "1") in
        let v1 = Word (Val "2") and v2 = Word (Val "3") in
        let p1 = [PUSH v1; PUSH k; SSTORE] and p2 = [PUSH v2; PUSH k; SSTORE] in
        let p = p1 @ p2 in
        let ea = Enc_consts.mk p (`User []) in
        let st = mk_state ea "" in
        let c = foralls (forall_vars ea) (enc_program ea st) in
        let m = solve_model_exn [c] in
        let xsstore0 = Word.enc_int 1 and xsstore1 = Word.enc_int 4 in
        assert_equal ~cmp:[%eq: Z3.Expr.t list] ~printer:(List.to_string ~f:Z3.Expr.to_string)
          [(Word.enc_int 2); (Word.enc_int 3)]
          [(eval_storage ~xs:[xsstore0; xsstore1] st m (Program.length p1) (Pusharg.enc ea.a (num 0) k));
           (eval_storage ~xs:[xsstore0; xsstore1] st m (Program.length p) (Pusharg.enc ea.a (num 0) k))]
      );

    "SSTORE input from stack" >:: (fun _ ->
        let k = Word (Val "1") in
        let p = [PUSH k; SSTORE] in
        let ea = Enc_consts.mk p (`User []) in
        let st = mk_state ea "" in
        let c = foralls (forall_vars ea) (enc_program ea st) in
        let m = solve_model_exn [c] in
        let xsstore0 = Word.enc_int 2 and x0 = Word.enc_int 3 in
        assert_equal ~cmp:[%eq: Z3.Expr.t list] ~printer:(List.to_string ~f:Z3.Expr.to_string)
          [xsstore0; x0]
          [(eval_storage ~xs:[x0; xsstore0] st m (PC.of_int 0) (Pusharg.enc ea.a (num 0) k));
           (eval_storage ~xs:[x0; xsstore0] st m (Program.length p) (Pusharg.enc ea.a (num 0) k))]
      );

    "SSTORE NUMBER" >:: (fun _ ->
        let k = Word (Val "1") in
        let p = [NUMBER; PUSH k; SSTORE] in
        let ea = Enc_consts.mk p (`User []) in
        let st = mk_state ea "" in
        let c = foralls (forall_vars ea) (enc_program ea st) in
        let m = solve_model_exn [c] in
        let xsstore0 = Word.enc_int 2 and number0 = Word.enc_int 3 in
        assert_equal ~cmp:[%eq: Z3.Expr.t list] ~printer:(List.to_string ~f:Z3.Expr.to_string)
          [xsstore0; number0]
          [(eval_storage ~xs:[xsstore0; number0] st m (PC.of_int 0) (Pusharg.enc ea.a (num 0) k));
           (eval_storage ~xs:[xsstore0; number0] st m (Program.length p) (Pusharg.enc ea.a (num 0) k))]
      );
  ]

let superoptimize =
  [
    "sload from same key twice" >:: (fun _ ->
        let key = Word (Val "1") in
        let p = [PUSH key; SLOAD; PUSH key; SLOAD] in
        let cis = `User [PUSH Tmpl; SLOAD; DUP I] in
        let ea = Enc_consts.mk p cis in
        let c = enc_super_opt ea in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: Program.t] ~printer:[%show: Program.t]
          [PUSH key; SLOAD; DUP I] (dec_super_opt ea m)
      );

    "sload from same computed key twice" >:: (fun _ ->
        let key = Word (Val "2") in
        let p = [PUSH key; SLOAD; PUSH (Word (Val "1")); PUSH (Word (Val "1")); ADD; SLOAD] in
        let cis = `User [PUSH Tmpl; SLOAD; DUP I] in
        let ea = Enc_consts.mk p cis in
        let c = enc_super_opt ea in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: Program.t] ~printer:[%show: Program.t]
          [PUSH key; SLOAD; DUP I] (dec_super_opt ea m)
      );

    "sload from two different keys is optimal" >:: (fun _ ->
        let key1 = Word (Val "1") in
        let key2 = Word (Val "2") in
        let p = [PUSH key1; SLOAD; PUSH key2; SLOAD] in
        let cis = `User [PUSH Tmpl; SLOAD; DUP I] in
        let ea = Enc_consts.mk p cis in
        let c = enc_super_opt ea in
        assert_bool "not unsat" (is_unsat [c])
      );

    "sload from two different computed keys" >: test_case ~length:Long (fun _ ->
        let key1 = Word (Val "1") in
        let key2 = Word (Val "2") in
        let p = [PUSH key1; SLOAD; PUSH (Word (Val "1")); PUSH (Word (Val "1")); ADD; SLOAD] in
        let cis = `User [PUSH Tmpl; SLOAD; ADD] in
        let ea = Enc_consts.mk p cis in
        let c = enc_super_opt ea in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: Program.t] ~printer:[%show: Program.t]
          [PUSH key1; SLOAD; PUSH key2; SLOAD] (dec_super_opt ea m)
      );

    "sload sstored value" >:: (fun _ ->
        let value = Word (Val "1") in
        let key = Word (Val "2") in
        let p = [PUSH value; PUSH key; SSTORE; PUSH key; SLOAD] in
        let cis = `User [PUSH Tmpl; SSTORE; SLOAD] in
        let ea = Enc_consts.mk p cis in
        let c = enc_super_opt ea in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: Program.t] ~printer:[%show: Program.t]
          [PUSH value; PUSH key; SSTORE; PUSH value] (dec_super_opt ea m)
      );

    "sstore sloaded value" >:: (fun _ ->
        let key = Word (Val "2") in
        let p = [PUSH key; SLOAD; PUSH key; SSTORE] in
        let cis = `User [PUSH Tmpl; SSTORE; SLOAD] in
        let ea = Enc_consts.mk p cis in
        let c = enc_super_opt ea in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: Program.t] ~printer:[%show: Program.t]
          [] (dec_super_opt ea m)
      );

    "overwrite sstored value" >:: (fun _ ->
        let value1 = Word (Val "1") and value2 = Word (Val "2") in
        let key = Word (Val "3") in
        let p = [PUSH value1; PUSH key; SSTORE; PUSH value2; PUSH key; SSTORE] in
        let cis = `User [PUSH Tmpl; SSTORE] in
        let ea = Enc_consts.mk p cis in
        let c = enc_super_opt ea in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: Program.t] ~printer:[%show: Program.t]
          [PUSH value2; PUSH key; SSTORE] (dec_super_opt ea m)
      );

    "sstore to two different keys is optimal" >:: (fun _ ->
        let key1 = Word (Val "1") in
        let key2 = Word (Val "2") in
        let value = Word (Val "3") in
        let p = [PUSH value; PUSH key1; SSTORE; PUSH value; PUSH key2; SSTORE] in
        let cis = `User [PUSH Tmpl; SSTORE; DUP I] in
        let ea = Enc_consts.mk p cis in
        let c = enc_super_opt ea in
        assert_bool "not unsat" (is_unsat [c])
      );

    "sstore value produced by input" >:: (fun _ ->
        let key = Word (Val "3") in
        let p = [PUSH key; SSTORE; PUSH (Word (Val "2")); POP] in
        let cis = `User [PUSH Tmpl; SSTORE] in
        let ea = Enc_consts.mk p cis in
        let c = enc_super_opt ea in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: Program.t] ~printer:[%show: Program.t]
          [PUSH key; SSTORE] (dec_super_opt ea m)
      );

    "sstore value produced by uninterpreted constant instruction" >:: (fun _ ->
        let key = Word (Val "3") in
        let p = [PUSH (Word (Val "1")); POP; NUMBER; PUSH key; SSTORE] in
        let cis = `User [PUSH Tmpl; SSTORE; NUMBER] in
        let ea = Enc_consts.mk p cis in
        let c = enc_super_opt ea in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: Program.t] ~printer:[%show: Program.t]
          [NUMBER; PUSH key; SSTORE] (dec_super_opt ea m)
      );

    "sstore value produced by uninterpreted instruction" >:: (fun _ ->
        let key = Word (Val "3") in
        let p = [PUSH (Word (Val "1")); PUSH (Word (Val "1")); ADD; BLOCKHASH; PUSH key; SSTORE] in
        let cis = `User [PUSH Tmpl; SSTORE; BLOCKHASH] in
        let ea = Enc_consts.mk p cis in
        let c = enc_super_opt ea in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: Program.t] ~printer:[%show: Program.t]
          [PUSH (Word (Val "2")); BLOCKHASH; PUSH key; SSTORE] (dec_super_opt ea m)
      );

    "sload as argument for uninterpreted instruction" >:: (fun _ ->
        let key = Word (Val "3") in
        let p = [PUSH key; SLOAD; BLOCKHASH; PUSH key; POP] in
        let cis = `User [PUSH Tmpl; SLOAD; BLOCKHASH] in
        let ea = Enc_consts.mk p cis in
        let c = enc_super_opt ea in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: Program.t] ~printer:[%show: Program.t]
          [PUSH key; SLOAD; BLOCKHASH;] (dec_super_opt ea m)
      );
  ]

let suite =
  (* set low for fast testing *)
  Word.set_wsz 2; SI.set_sas 6;
  "suite" >:::
  effect @ gas_cost @ superoptimize

let () =
  run_test_tt_main suite
