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
open Program
open Enc_consts
open Evm_state

(* returns value within bounds of word size *)
let val_of_int_safe i = Pusharg.Word (Val (Int.to_string (i mod !Word.size)))

let test_stack_pres oc =
  let (d, _) = delta_alpha oc in
  (* create program that initializes stack with d + 2 values *)
  let ip = List.init (d + 2) ~f:(fun i -> PUSH (val_of_int_safe i)) in
  let p = ip @ [oc] in
  let ea = Enc_consts.mk p (`User []) in
  let st = Evm_state.mk ea "" in
  let c = foralls (forall_vars ea) (enc_program ea st) in
  let m = solve_model_exn [c] in
  (* check all words below delta *)
  assert_equal ~cmp:[%eq: Z3.Expr.t list]
    ~printer:(List.to_string ~f:Z3.Expr.to_string)
    [(Word.enc_int 0); (Word.enc_int 1)]
    [(eval_stack ~xs:(List.map (forall_vars ea) ~f:(fun _ -> Word.enc_int 1)) st m (Program.length p) 0);
     (eval_stack ~xs:(List.map (forall_vars ea) ~f:(fun _ -> Word.enc_int 1)) st m (Program.length p) 1)]

let test_stack_ctr p =
  let d = stack_depth p in
  (* create program that initializes stack with d values *)
  let ip = List.init d ~f:(fun i -> PUSH (val_of_int_safe i)) in
  let p = ip @ p in
  let ea = Enc_consts.mk p (`User []) in
  let st = Evm_state.mk ea "" in
  let c = enc_program ea st in
  let m = solve_model_exn [c] in
  let upd_sc sc oc = let (d, a) = delta_alpha oc in sc - d + a in
  (* check that stack counter is adjusted accordingly *)
  assert_equal ~cmp:[%eq: Z3.Expr.t] ~printer:Z3.Expr.to_string
    (SI.enc (List.fold_left p ~init:0 ~f:upd_sc))
    (eval_stack_ctr st m (Program.length p))

let test_no_exc_halt p =
  let d = stack_depth p in
  (* create program that initializes stack with d values *)
  let ip = List.init d ~f:(fun i -> PUSH (val_of_int_safe i)) in
  let p = ip @ p in
  let ea = Enc_consts.mk p (`User []) in
  let st = Evm_state.mk ea "" in
  let c = enc_program ea st in
  let m = solve_model_exn [c] in
  (* check no exceptional halting occured *)
  assert_equal ~cmp:[%eq: Z3.Expr.t] ~printer:Z3.Expr.to_string
    btm
    (eval_exc_halt st m (Program.length p))

let test_exc_halt_pres p =
  let max = Int.pow 2 !SI.size in
  let ip = List.init max ~f:(fun _ -> PUSH (Word (Val "1"))) in
  let p = ip @ p in
  let ea = Enc_consts.mk p (`User []) in
  let st = Evm_state.mk ea "" in
  let c = enc_program ea st in
  let m = solve_model_exn [c] in
  assert_equal
    ~cmp:[%eq: Z3.Expr.t]
    ~printer:Z3.Expr.to_string
    top
    (eval_exc_halt st m (Program.length p))

let effect =
  [
    (* add *)

    "add two words on the stack">:: (fun _ ->
        let p = [PUSH (Word (Val "1")); PUSH (Word (Val "2")); ADD] in
        let ea = Enc_consts.mk p (`User []) in
        let st = Evm_state.mk ea "" in
        let c = enc_program ea st in
        let m = solve_model_exn [c] in
        assert_equal
          ~cmp:[%eq: Z3.Expr.t]
          ~printer:Z3.Expr.to_string
          (Word.enc_int 3)
          (eval_stack st m (Program.length p) 0)
      );

    (* sub *)

    "subtract two words on the stack">:: (fun _ ->
        let p = [PUSH (Word (Val "3")); PUSH (Word (Val "4")); SUB] in
        let ea = Enc_consts.mk p (`User []) in
        let st = Evm_state.mk ea "" in
        let c = enc_program ea st in
        let m = solve_model_exn [c] in
        assert_equal
          ~cmp:[%eq: Z3.Expr.t]
          ~printer:Z3.Expr.to_string
          (Word.enc_int 1)
          (eval_stack st m (Program.length p) 0)
      );

    "subtract two words on the stack with negative result">:: (fun _ ->
        let p = [PUSH (Word (Val "4")); PUSH (Word (Val "3")); SUB] in
        let ea = Enc_consts.mk p (`User []) in
        let st = Evm_state.mk ea "" in
        let c = enc_program ea st in
        let m = solve_model_exn [c] in
        assert_equal
          ~cmp:[%eq: Z3.Expr.t]
          ~printer:Z3.Expr.to_string
          (Word.enc_int (-1))
          (eval_stack st m (Program.length p) 0)
      );

    (* add and sub *)

    "combine add and sub">:: (fun _ ->
        let p = [PUSH (Word (Val "3")); PUSH (Word (Val "2")); PUSH (Word (Val "2")); ADD; SUB] in
        let ea = Enc_consts.mk p (`User []) in
        let st = Evm_state.mk ea "" in
        let c = enc_program ea st in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: Z3.Expr.t] ~printer:Z3.Expr.to_string
          (Word.enc_int 1) (eval_stack st m (Program.length p) 0)
      );

    (* div *)

    "divide 1 by 1" >::(fun _ ->
        let p = [PUSH (Word (Val "1")); PUSH (Word (Val "1")); DIV] in
        let ea = Enc_consts.mk p (`User []) in
        let st = Evm_state.mk ea "" in
        let c = enc_program ea st in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: Z3.Expr.t] ~printer:Z3.Expr.to_string
          (Word.enc_int 1) (eval_stack st m (Program.length p) 0)
      );

    "divide 4 by 2" >::(fun _ ->
        let p = [PUSH (Word (Val "2")); PUSH (Word (Val "4")); DIV] in
        let ea = Enc_consts.mk p (`User []) in
        let st = Evm_state.mk ea "" in
        let c = enc_program ea st in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: Z3.Expr.t] ~printer:Z3.Expr.to_string
          (Word.enc_int 2) (eval_stack st m (Program.length p) 0)
      );

    "divide 5 by 2" >::(fun _ ->
        let p = [PUSH (Word (Val "2")); PUSH (Word (Val "5")); DIV] in
        let ea = Enc_consts.mk p (`User []) in
        let st = Evm_state.mk ea "" in
        let c = enc_program ea st in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: Z3.Expr.t] ~printer:Z3.Expr.to_string
          (Word.enc_int 2) (eval_stack st m (Program.length p) 0)
      );

    "divide 2 by 4" >::(fun _ ->
        let p = [PUSH (Word (Val "4")); PUSH (Word (Val "2")); DIV] in
        let ea = Enc_consts.mk p (`User []) in
        let st = Evm_state.mk ea "" in
        let c = enc_program ea st in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: Z3.Expr.t] ~printer:Z3.Expr.to_string
          (Word.enc_int 0) (eval_stack st m (Program.length p) 0)
      );

    "divide 2 by 0" >::(fun _ ->
        let p = [PUSH (Word (Val "0")); PUSH (Word (Val "2")); DIV] in
        let ea = Enc_consts.mk p (`User []) in
        let st = Evm_state.mk ea "" in
        let c = enc_program ea st in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: Z3.Expr.t] ~printer:Z3.Expr.to_string
          (Word.enc_int 0) (eval_stack st m (Program.length p) 0)
      );

    "divide 0 by 0" >::(fun _ ->
        let p = [PUSH (Word (Val "0")); PUSH (Word (Val "0")); DIV] in
        let ea = Enc_consts.mk p (`User []) in
        let st = Evm_state.mk ea "" in
        let c = enc_program ea st in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: Z3.Expr.t] ~printer:Z3.Expr.to_string
          (Word.enc_int 0) (eval_stack st m (Program.length p) 0)
      );

    (* sdiv *)

    "1 sdiv 0 = 0" >::(fun _ ->
        let p = [PUSH (Word (Val "0")); PUSH (Word (Val "1")); SDIV] in
        let ea = Enc_consts.mk p (`User []) in
        let st = Evm_state.mk ea "" in
        let c = enc_program ea st in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: Z3.Expr.t] ~printer:Z3.Expr.to_string
          (Word.enc_int 0) (eval_stack st m (Program.length p) 0)
      );

    "3 sdiv 2 = 1" >::(fun _ ->
        let p = [PUSH (Word (Val "2")); PUSH (Word (Val "3")); SDIV] in
        let ea = Enc_consts.mk p (`User []) in
        let st = Evm_state.mk ea "" in
        let c = enc_program ea st in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: Z3.Expr.t] ~printer:Z3.Expr.to_string
          (Word.enc_int 1) (eval_stack st m (Program.length p) 0)
      );

    "-3 sdiv 2 = -1" >::(fun _ ->
        let p = [PUSH (Word (Val "2")); PUSH (Word (Val "-3")); SDIV] in
        let ea = Enc_consts.mk p (`User []) in
        let st = Evm_state.mk ea "" in
        let c = enc_program ea st in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: Z3.Expr.t] ~printer:Z3.Expr.to_string
          (Word.enc_int (-1)) (eval_stack st m (Program.length p) 0)
      );

    "3 sdiv -2 = -1" >::(fun _ ->
        let p = [PUSH (Word (Val "-2")); PUSH (Word (Val "3")); SDIV] in
        let ea = Enc_consts.mk p (`User []) in
        let st = Evm_state.mk ea "" in
        let c = enc_program ea st in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: Z3.Expr.t] ~printer:Z3.Expr.to_string
          (Word.enc_int (-1)) (eval_stack st m (Program.length p) 0)
      );

    "-3 sdiv -2 = 1" >::(fun _ ->
        let p = [PUSH (Word (Val "-2")); PUSH (Word (Val "-3")); SDIV] in
        let ea = Enc_consts.mk p (`User []) in
        let st = Evm_state.mk ea "" in
        let c = enc_program ea st in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: Z3.Expr.t] ~printer:Z3.Expr.to_string
          (Word.enc_int 1) (eval_stack st m (Program.length p) 0)
      );

    "-1 sdiv -1 = 1" >::(fun _ ->
        let p = [PUSH (Word (Val "-1")); PUSH (Word (Val "-1")); SDIV] in
        let ea = Enc_consts.mk p (`User []) in
        let st = Evm_state.mk ea "" in
        let c = enc_program ea st in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: Z3.Expr.t] ~printer:Z3.Expr.to_string
          (Word.enc_int 1) (eval_stack st m (Program.length p) 0)
      );

    "-1 sdiv 2 = 0" >::(fun _ ->
        let p = [PUSH (Word (Val "2")); PUSH (Word (Val "-1")); SDIV] in
        let ea = Enc_consts.mk p (`User []) in
        let st = Evm_state.mk ea "" in
        let c = enc_program ea st in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: Z3.Expr.t] ~printer:Z3.Expr.to_string
          (Word.enc_int 0) (eval_stack st m (Program.length p) 0)
      );

    "-2^(wsz - 1) sdiv -1 = -2^(wsz - 1), wraps to negative" >::(fun _ ->
        let p = [PUSH (Word (Val "-1")); PUSH (Word (Val "0b100")); SDIV] in
        let ea = Enc_consts.mk p (`User []) in
        let st = Evm_state.mk ea "" in
        let c = enc_program ea st in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: Z3.Expr.t] ~printer:Z3.Expr.to_string
          (Word.enc_int (-4)) (eval_stack st m (Program.length p) 0)
      );

    (* mod *)

    "2 modulo 1" >::(fun _ ->
        let p = [PUSH (Word (Val "1")); PUSH (Word (Val "2")); MOD] in
        let ea = Enc_consts.mk p (`User []) in
        let st = Evm_state.mk ea "" in
        let c = enc_program ea st in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: Z3.Expr.t] ~printer:Z3.Expr.to_string
          (Word.enc_int 0) (eval_stack st m (Program.length p) 0)
      );

    "4 modulo 2" >::(fun _ ->
        let p = [PUSH (Word (Val "2")); PUSH (Word (Val "4")); MOD] in
        let ea = Enc_consts.mk p (`User []) in
        let st = Evm_state.mk ea "" in
        let c = enc_program ea st in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: Z3.Expr.t] ~printer:Z3.Expr.to_string
          (Word.enc_int 0) (eval_stack st m (Program.length p) 0)
      );

    "5 modulo 2" >::(fun _ ->
        let p = [PUSH (Word (Val "2")); PUSH (Word (Val "5")); MOD] in
        let ea = Enc_consts.mk p (`User []) in
        let st = Evm_state.mk ea "" in
        let c = enc_program ea st in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: Z3.Expr.t] ~printer:Z3.Expr.to_string
          (Word.enc_int 1) (eval_stack st m (Program.length p) 0)
      );

    "2 modulo 4" >::(fun _ ->
        let p = [PUSH (Word (Val "4")); PUSH (Word (Val "2")); MOD] in
        let ea = Enc_consts.mk p (`User []) in
        let st = Evm_state.mk ea "" in
        let c = enc_program ea st in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: Z3.Expr.t] ~printer:Z3.Expr.to_string
          (Word.enc_int 2) (eval_stack st m (Program.length p) 0)
      );

    "2 modulo 0" >::(fun _ ->
        let p = [PUSH (Word (Val "0")); PUSH (Word (Val "2")); MOD] in
        let ea = Enc_consts.mk p (`User []) in
        let st = Evm_state.mk ea "" in
        let c = enc_program ea st in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: Z3.Expr.t] ~printer:Z3.Expr.to_string
          (Word.enc_int 0) (eval_stack st m (Program.length p) 0)
      );

    "0 modulo 0" >::(fun _ ->
        let p = [PUSH (Word (Val "0")); PUSH (Word (Val "0")); MOD] in
        let ea = Enc_consts.mk p (`User []) in
        let st = Evm_state.mk ea "" in
        let c = enc_program ea st in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: Z3.Expr.t] ~printer:Z3.Expr.to_string
          (Word.enc_int 0) (eval_stack st m (Program.length p) 0)
      );

    (* smod *)

    "3 smodulo 2 is 1" >::(fun _ ->
        let p = [PUSH (Word (Val "2")); PUSH (Word (Val "3")); SMOD] in
        let ea = Enc_consts.mk p (`User []) in
        let st = Evm_state.mk ea "" in
        let c = enc_program ea st in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: Z3.Expr.t] ~printer:Z3.Expr.to_string
          (Word.enc_int 1) (eval_stack st m (Program.length p) 0)
      );

    "-2 smodulo 3 is -2" >::(fun _ ->
        let p = [PUSH (Word (Val "3")); PUSH (Word (Val "-2")); SMOD] in
        let ea = Enc_consts.mk p (`User []) in
        let st = Evm_state.mk ea "" in
        let c = enc_program ea st in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: Z3.Expr.t] ~printer:Z3.Expr.to_string
          (Word.enc_int (-2)) (eval_stack st m (Program.length p) 0)
      );

    "-2 smodulo 1 is 0" >::(fun _ ->
        let p = [PUSH (Word (Val "1")); PUSH (Word (Val "-2")); SMOD] in
        let ea = Enc_consts.mk p (`User []) in
        let st = Evm_state.mk ea "" in
        let c = enc_program ea st in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: Z3.Expr.t] ~printer:Z3.Expr.to_string
          (Word.enc_int 0) (eval_stack st m (Program.length p) 0)
      );

    "2 smodulo -1 is 0" >::(fun _ ->
        let p = [PUSH (Word (Val "-1")); PUSH (Word (Val "2")); SMOD] in
        let ea = Enc_consts.mk p (`User []) in
        let st = Evm_state.mk ea "" in
        let c = enc_program ea st in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: Z3.Expr.t] ~printer:Z3.Expr.to_string
          (Word.enc_int 0) (eval_stack st m (Program.length p) 0)
      );

    "-3 smodulo 2 is -1" >::(fun _ ->
        let p = [PUSH (Word (Val "2")); PUSH (Word (Val "-3")); SMOD] in
        let ea = Enc_consts.mk p (`User []) in
        let st = Evm_state.mk ea "" in
        let c = enc_program ea st in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: Z3.Expr.t] ~printer:Z3.Expr.to_string
          (Word.enc_int (-1)) (eval_stack st m (Program.length p) 0)
      );

    "3 smodulo -2 is 1" >::(fun _ ->
        let p = [PUSH (Word (Val "-2")); PUSH (Word (Val "3")); SMOD] in
        let ea = Enc_consts.mk p (`User []) in
        let st = Evm_state.mk ea "" in
        let c = enc_program ea st in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: Z3.Expr.t] ~printer:Z3.Expr.to_string
          (Word.enc_int 1) (eval_stack st m (Program.length p) 0)
      );

    "-4 smodulo 2 is 0 (largest negative number)" >::(fun _ ->
        let p = [PUSH (Word (Val "2")); PUSH (Word (Val "-4")); SMOD] in
        let ea = Enc_consts.mk p (`User []) in
        let st = Evm_state.mk ea "" in
        let c = enc_program ea st in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: Z3.Expr.t] ~printer:Z3.Expr.to_string
          (Word.enc_int 0) (eval_stack st m (Program.length p) 0)
      );

    "-3 smodulo 0 is 0" >::(fun _ ->
        let p = [PUSH (Word (Val "0")); PUSH (Word (Val "-3")); SMOD] in
        let ea = Enc_consts.mk p (`User []) in
        let st = Evm_state.mk ea "" in
        let c = enc_program ea st in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: Z3.Expr.t] ~printer:Z3.Expr.to_string
          (Word.enc_int 0) (eval_stack st m (Program.length p) 0)
      );

    "3 smodulo 0 is 0" >::(fun _ ->
        let p = [PUSH (Word (Val "0")); PUSH (Word (Val "3")); SMOD] in
        let ea = Enc_consts.mk p (`User []) in
        let st = Evm_state.mk ea "" in
        let c = enc_program ea st in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: Z3.Expr.t] ~printer:Z3.Expr.to_string
          (Word.enc_int 0) (eval_stack st m (Program.length p) 0)
      );

    (* addmod *)

    "(2 + 1) mod 2 = 1" >::(fun _ ->
        let p = [PUSH (Word (Val "2")); PUSH (Word (Val "1")); PUSH (Word (Val "2")); ADDMOD] in
        let ea = Enc_consts.mk p (`User []) in
        let st = Evm_state.mk ea "" in
        let c = enc_program ea st in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: Z3.Expr.t] ~printer:Z3.Expr.to_string
          (Word.enc_int 1) (eval_stack st m (Program.length p) 0)
      );

    "(7 + 1) mod 3 = 2 (overflow which should be ignored)" >::(fun _ ->
        let p = [PUSH (Word (Val "3")); PUSH (Word (Val "1")); PUSH (Word (Val "7")); ADDMOD] in
        let ea = Enc_consts.mk p (`User []) in
        let st = Evm_state.mk ea "" in
        let c = enc_program ea st in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: Z3.Expr.t] ~printer:Z3.Expr.to_string
          (Word.enc_int 2) (eval_stack st m (Program.length p) 0)
      );

    "(1 + 1) mod 3 = 2" >::(fun _ ->
        let p = [PUSH (Word (Val "3")); PUSH (Word (Val "1")); PUSH (Word (Val "1")); ADDMOD] in
        let ea = Enc_consts.mk p (`User []) in
        let st = Evm_state.mk ea "" in
        let c = enc_program ea st in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: Z3.Expr.t] ~printer:Z3.Expr.to_string
          (Word.enc_int 2) (eval_stack st m (Program.length p) 0)
      );

    "(1 + 1) mod 2 = 0" >::(fun _ ->
        let p = [PUSH (Word (Val "2")); PUSH (Word (Val "1")); PUSH (Word (Val "1")); ADDMOD] in
        let ea = Enc_consts.mk p (`User []) in
        let st = Evm_state.mk ea "" in
        let c = enc_program ea st in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: Z3.Expr.t] ~printer:Z3.Expr.to_string
          (Word.enc_int 0) (eval_stack st m (Program.length p) 0)
      );

    "(0 + 1) mod 0 = 0" >::(fun _ ->
        let p = [PUSH (Word (Val "0")); PUSH (Word (Val "1")); PUSH (Word (Val "0")); ADDMOD] in
        let ea = Enc_consts.mk p (`User []) in
        let st = Evm_state.mk ea "" in
        let c = enc_program ea st in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: Z3.Expr.t] ~printer:Z3.Expr.to_string
          (Word.enc_int 0) (eval_stack st m (Program.length p) 0)
      );

    "(7 + 1) mod 2 = 0 (overflow which should be ignored)" >::(fun _ ->
        let p = [PUSH (Word (Val "2")); PUSH (Word (Val "1")); PUSH (Word (Val "7")); ADDMOD] in
        let ea = Enc_consts.mk p (`User []) in
        let st = Evm_state.mk ea "" in
        let c = enc_program ea st in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: Z3.Expr.t] ~printer:Z3.Expr.to_string
          (Word.enc_int 0) (eval_stack st m (Program.length p) 0)
      );

    "(-1 + 1) mod 2 = 0" >::(fun _ ->
        let p = [PUSH (Word (Val "2")); PUSH (Word (Val "1")); PUSH (Word (Val "-1")); ADDMOD] in
        let ea = Enc_consts.mk p (`User []) in
        let st = Evm_state.mk ea "" in
        let c = enc_program ea st in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: Z3.Expr.t] ~printer:Z3.Expr.to_string
          (Word.enc_int 0) (eval_stack st m (Program.length p) 0)
      );

    (* mulmod *)

    "(2 * 1) mod 2 = 0" >::(fun _ ->
        let p = [PUSH (Word (Val "2")); PUSH (Word (Val "1")); PUSH (Word (Val "2")); MULMOD] in
        let ea = Enc_consts.mk p (`User []) in
        let st = Evm_state.mk ea "" in
        let c = enc_program ea st in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: Z3.Expr.t] ~printer:Z3.Expr.to_string
          (Word.enc_int 0) (eval_stack st m (Program.length p) 0)
      );

    "(7 * 7) mod 2 = 1 (overflow happens)" >::(fun _ ->
        let p = [PUSH (Word (Val "2")); PUSH (Word (Val "7")); PUSH (Word (Val "7")); MULMOD] in
        let ea = Enc_consts.mk p (`User []) in
        let st = Evm_state.mk ea "" in
        let c = enc_program ea st in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: Z3.Expr.t] ~printer:Z3.Expr.to_string
          (Word.enc_int 1) (eval_stack st m (Program.length p) 0)
      );

    "(7 * 6) mod 7 = 0 (overflow happens)" >::(fun _ ->
        let p = [PUSH (Word (Val "7")); PUSH (Word (Val "6")); PUSH (Word (Val "7")); MULMOD] in
        let ea = Enc_consts.mk p (`User []) in
        let st = Evm_state.mk ea "" in
        let c = enc_program ea st in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: Z3.Expr.t] ~printer:Z3.Expr.to_string
          (Word.enc_int 0) (eval_stack st m (Program.length p) 0)
      );

    "(2 * 1) mod 0 = 0" >::(fun _ ->
        let p = [PUSH (Word (Val "0")); PUSH (Word (Val "1")); PUSH (Word (Val "2")); MULMOD] in
        let ea = Enc_consts.mk p (`User []) in
        let st = Evm_state.mk ea "" in
        let c = enc_program ea st in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: Z3.Expr.t] ~printer:Z3.Expr.to_string
          (Word.enc_int 0) (eval_stack st m (Program.length p) 0)
      );

    "(0 * 5) mod 2 = 0" >::(fun _ ->
        let p = [PUSH (Word (Val "2")); PUSH (Word (Val "5")); PUSH (Word (Val "0")); MULMOD] in
        let ea = Enc_consts.mk p (`User []) in
        let st = Evm_state.mk ea "" in
        let c = enc_program ea st in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: Z3.Expr.t] ~printer:Z3.Expr.to_string
          (Word.enc_int 0) (eval_stack st m (Program.length p) 0)
      );

    (* iszero *)

    "0 iszero is true" >::(fun _ ->
        let p = [PUSH (Word (Val "0")); ISZERO] in
        let ea = Enc_consts.mk p (`User []) in
        let st = Evm_state.mk ea "" in
        let c = enc_program ea st in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: Z3.Expr.t] ~printer:Z3.Expr.to_string
          (Word.enc_int 1) (eval_stack st m (Program.length p) 0)
      );

    "1 iszero is false" >::(fun _ ->
        let p = [PUSH (Word (Val "1")); ISZERO] in
        let ea = Enc_consts.mk p (`User []) in
        let st = Evm_state.mk ea "" in
        let c = enc_program ea st in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: Z3.Expr.t] ~printer:Z3.Expr.to_string
          (Word.enc_int 0) (eval_stack st m (Program.length p) 0)
      );

    "0 - 5 iszero is false" >::(fun _ ->
        let p = [PUSH (Word (Val "5")); PUSH (Word (Val "0")); SUB; ISZERO] in
        let ea = Enc_consts.mk p (`User []) in
        let st = Evm_state.mk ea "" in
        let c = enc_program ea st in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: Z3.Expr.t] ~printer:Z3.Expr.to_string
          (Word.enc_int 0) (eval_stack st m (Program.length p) 0)
      );

    (* and *)

    "0 & 1 is 0" >::(fun _ ->
        let p = [PUSH (Word (Val "1")); PUSH (Word (Val "0")); AND] in
        let ea = Enc_consts.mk p (`User []) in
        let st = Evm_state.mk ea "" in
        let c = enc_program ea st in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: Z3.Expr.t] ~printer:Z3.Expr.to_string
          (Word.enc_int 0) (eval_stack st m (Program.length p) 0)
      );

    "1 & 1 is 1" >::(fun _ ->
        let p = [PUSH (Word (Val "1")); PUSH (Word (Val "1")); AND] in
        let ea = Enc_consts.mk p (`User []) in
        let st = Evm_state.mk ea "" in
        let c = enc_program ea st in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: Z3.Expr.t] ~printer:Z3.Expr.to_string
          (Word.enc_int 1) (eval_stack st m (Program.length p) 0)
      );

    "0 & 0 is 0" >::(fun _ ->
        let p = [PUSH (Word (Val "0")); PUSH (Word (Val "0")); AND] in
        let ea = Enc_consts.mk p (`User []) in
        let st = Evm_state.mk ea "" in
        let c = enc_program ea st in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: Z3.Expr.t] ~printer:Z3.Expr.to_string
          (Word.enc_int 0) (eval_stack st m (Program.length p) 0)
      );

    "1 & 0 is 0" >::(fun _ ->
        let p = [PUSH (Word (Val "1")); PUSH (Word (Val "0")); AND] in
        let ea = Enc_consts.mk p (`User []) in
        let st = Evm_state.mk ea "" in
        let c = enc_program ea st in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: Z3.Expr.t] ~printer:Z3.Expr.to_string
          (Word.enc_int 0) (eval_stack st m (Program.length p) 0)
      );

    "AND is idempotent (0b101)" >::(fun _ ->
        let p = [PUSH (Word (Val "0b101")); PUSH (Word (Val "0b101")); AND] in
        let ea = Enc_consts.mk p (`User []) in
        let st = Evm_state.mk ea "" in
        let c = enc_program ea st in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: Z3.Expr.t] ~printer:Z3.Expr.to_string
          (Word.enc_int 5) (eval_stack st m (Program.length p) 0)
      );

    "0b111 & 0b100 is 0b100" >::(fun _ ->
        let p = [PUSH (Word (Val "0b111")); PUSH (Word (Val "0b100")); AND] in
        let ea = Enc_consts.mk p (`User []) in
        let st = Evm_state.mk ea "" in
        let c = enc_program ea st in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: Z3.Expr.t] ~printer:Z3.Expr.to_string
          (Word.enc_int 4) (eval_stack st m (Program.length p) 0)
      );

    (* or *)

    "0 | 1 is 1" >::(fun _ ->
        let p = [PUSH (Word (Val "0")); PUSH (Word (Val "1")); OR] in
        let ea = Enc_consts.mk p (`User []) in
        let st = Evm_state.mk ea "" in
        let c = enc_program ea st in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: Z3.Expr.t] ~printer:Z3.Expr.to_string
          (Word.enc_int 1) (eval_stack st m (Program.length p) 0)
      );

    "1 | 1 is 1" >::(fun _ ->
        let p = [PUSH (Word (Val "1")); PUSH (Word (Val "1")); OR] in
        let ea = Enc_consts.mk p (`User []) in
        let st = Evm_state.mk ea "" in
        let c = enc_program ea st in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: Z3.Expr.t] ~printer:Z3.Expr.to_string
          (Word.enc_int 1) (eval_stack st m (Program.length p) 0)
      );

    "0 | 0 is 0" >::(fun _ ->
        let p = [PUSH (Word (Val "0")); PUSH (Word (Val "0")); OR] in
        let ea = Enc_consts.mk p (`User []) in
        let st = Evm_state.mk ea "" in
        let c = enc_program ea st in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: Z3.Expr.t] ~printer:Z3.Expr.to_string
          (Word.enc_int 0) (eval_stack st m (Program.length p) 0)
      );

    "1 | 0 is 1" >::(fun _ ->
        let p = [PUSH (Word (Val "1")); PUSH (Word (Val "0")); OR] in
        let ea = Enc_consts.mk p (`User []) in
        let st = Evm_state.mk ea "" in
        let c = enc_program ea st in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: Z3.Expr.t] ~printer:Z3.Expr.to_string
          (Word.enc_int 1) (eval_stack st m (Program.length p) 0)
      );

    "OR is idempotent (0b101)" >::(fun _ ->
        let p = [PUSH (Word (Val "0b101")); PUSH (Word (Val "0b101")); OR] in
        let ea = Enc_consts.mk p (`User []) in
        let st = Evm_state.mk ea "" in
        let c = enc_program ea st in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: Z3.Expr.t] ~printer:Z3.Expr.to_string
          (Word.enc_int 5) (eval_stack st m (Program.length p) 0)
      );

    "0b001 | 0b100 is 0b101" >::(fun _ ->
        let p = [PUSH (Word (Val "0b001")); PUSH (Word (Val "0b100")); OR] in
        let ea = Enc_consts.mk p (`User []) in
        let st = Evm_state.mk ea "" in
        let c = enc_program ea st in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: Z3.Expr.t] ~printer:Z3.Expr.to_string
          (Word.enc_int 5) (eval_stack st m (Program.length p) 0)
      );

    (* xor *)

    "0 ^ 1 is 1" >::(fun _ ->
        let p = [PUSH (Word (Val "0")); PUSH (Word (Val "1")); XOR] in
        let ea = Enc_consts.mk p (`User []) in
        let st = Evm_state.mk ea "" in
        let c = enc_program ea st in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: Z3.Expr.t] ~printer:Z3.Expr.to_string
          (Word.enc_int 1) (eval_stack st m (Program.length p) 0)
      );

    "1 ^ 1 is 0" >::(fun _ ->
        let p = [PUSH (Word (Val "1")); PUSH (Word (Val "1")); XOR] in
        let ea = Enc_consts.mk p (`User []) in
        let st = Evm_state.mk ea "" in
        let c = enc_program ea st in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: Z3.Expr.t] ~printer:Z3.Expr.to_string
          (Word.enc_int 0) (eval_stack st m (Program.length p) 0)
      );

    "0 ^ 0 is 0" >::(fun _ ->
        let p = [PUSH (Word (Val "0")); PUSH (Word (Val "0")); XOR] in
        let ea = Enc_consts.mk p (`User []) in
        let st = Evm_state.mk ea "" in
        let c = enc_program ea st in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: Z3.Expr.t] ~printer:Z3.Expr.to_string
          (Word.enc_int 0) (eval_stack st m (Program.length p) 0)
      );

    "1 ^ 0 is 1" >::(fun _ ->
        let p = [PUSH (Word (Val "1")); PUSH (Word (Val "0")); XOR] in
        let ea = Enc_consts.mk p (`User []) in
        let st = Evm_state.mk ea "" in
        let c = enc_program ea st in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: Z3.Expr.t] ~printer:Z3.Expr.to_string
          (Word.enc_int 1) (eval_stack st m (Program.length p) 0)
      );

    "XOR is cancellative (0b101)" >::(fun _ ->
        let p = [PUSH (Word (Val "0b101")); PUSH (Word (Val "0b101")); XOR] in
        let ea = Enc_consts.mk p (`User []) in
        let st = Evm_state.mk ea "" in
        let c = enc_program ea st in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: Z3.Expr.t] ~printer:Z3.Expr.to_string
          (Word.enc_int 0) (eval_stack st m (Program.length p) 0)
      );

    "0b101 ^ 0b100 is 0b001" >::(fun _ ->
        let p = [PUSH (Word (Val "0b101")); PUSH (Word (Val "0b100")); XOR] in
        let ea = Enc_consts.mk p (`User []) in
        let st = Evm_state.mk ea "" in
        let c = enc_program ea st in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: Z3.Expr.t] ~printer:Z3.Expr.to_string
          (Word.enc_int 1) (eval_stack st m (Program.length p) 0)
      );

    (* eq *)

    "0 = 0 is 1" >::(fun _ ->
        let p = [PUSH (Word (Val "0")); PUSH (Word (Val "0")); EQ] in
        let ea = Enc_consts.mk p (`User []) in
        let st = Evm_state.mk ea "" in
        let c = enc_program ea st in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: Z3.Expr.t] ~printer:Z3.Expr.to_string
          (Word.enc_int 1) (eval_stack st m (Program.length p) 0)
      );

    "1 = 0 is 0" >::(fun _ ->
        let p = [PUSH (Word (Val "0")); PUSH (Word (Val "1")); EQ] in
        let ea = Enc_consts.mk p (`User []) in
        let st = Evm_state.mk ea "" in
        let c = enc_program ea st in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: Z3.Expr.t] ~printer:Z3.Expr.to_string
          (Word.enc_int 0) (eval_stack st m (Program.length p) 0)
      );

    "0 = 1 is 0" >::(fun _ ->
        let p = [PUSH (Word (Val "1")); PUSH (Word (Val "0")); EQ] in
        let ea = Enc_consts.mk p (`User []) in
        let st = Evm_state.mk ea "" in
        let c = enc_program ea st in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: Z3.Expr.t] ~printer:Z3.Expr.to_string
          (Word.enc_int 0) (eval_stack st m (Program.length p) 0)
      );

    "1 = 1 is 1" >::(fun _ ->
        let p = [PUSH (Word (Val "1")); PUSH (Word (Val "1")); EQ] in
        let ea = Enc_consts.mk p (`User []) in
        let st = Evm_state.mk ea "" in
        let c = enc_program ea st in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: Z3.Expr.t] ~printer:Z3.Expr.to_string
          (Word.enc_int 1) (eval_stack st m (Program.length p) 0)
      );

    "-1 = 1 is 0" >::(fun _ ->
        let p = [PUSH (Word (Val "1")); PUSH (Word (Val "-1")); EQ] in
        let ea = Enc_consts.mk p (`User []) in
        let st = Evm_state.mk ea "" in
        let c = enc_program ea st in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: Z3.Expr.t] ~printer:Z3.Expr.to_string
          (Word.enc_int 0) (eval_stack st m (Program.length p) 0)
      );

    (* lt *)

    "0 < 0 is 0" >::(fun _ ->
        let p = [PUSH (Word (Val "0")); PUSH (Word (Val "0")); LT] in
        let ea = Enc_consts.mk p (`User []) in
        let st = Evm_state.mk ea "" in
        let c = enc_program ea st in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: Z3.Expr.t] ~printer:Z3.Expr.to_string
          (Word.enc_int 0) (eval_stack st m (Program.length p) 0)
      );

    "1 < 0 is 0" >::(fun _ ->
        let p = [PUSH (Word (Val "0")); PUSH (Word (Val "1")); LT] in
        let ea = Enc_consts.mk p (`User []) in
        let st = Evm_state.mk ea "" in
        let c = enc_program ea st in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: Z3.Expr.t] ~printer:Z3.Expr.to_string
          (Word.enc_int 0) (eval_stack st m (Program.length p) 0)
      );

    "0 < 1 is 1" >::(fun _ ->
        let p = [PUSH (Word (Val "1")); PUSH (Word (Val "0")); LT] in
        let ea = Enc_consts.mk p (`User []) in
        let st = Evm_state.mk ea "" in
        let c = enc_program ea st in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: Z3.Expr.t] ~printer:Z3.Expr.to_string
          (Word.enc_int 1) (eval_stack st m (Program.length p) 0)
      );

    "1 < -1 is 1 (unsigned LT)" >::(fun _ ->
        let p = [PUSH (Word (Val "-1")); PUSH (Word (Val "1")); LT] in
        let ea = Enc_consts.mk p (`User []) in
        let st = Evm_state.mk ea "" in
        let c = enc_program ea st in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: Z3.Expr.t] ~printer:Z3.Expr.to_string
          (Word.enc_int 1) (eval_stack st m (Program.length p) 0)
      );

    "-1 < 1 is 0 (unsigned LT)" >::(fun _ ->
        let p = [PUSH (Word (Val "1")); PUSH (Word (Val "-1")); LT] in
        let ea = Enc_consts.mk p (`User []) in
        let st = Evm_state.mk ea "" in
        let c = enc_program ea st in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: Z3.Expr.t] ~printer:Z3.Expr.to_string
          (Word.enc_int 0) (eval_stack st m (Program.length p) 0)
      );

    (* gt *)

    "0 > 0 is 0" >::(fun _ ->
        let p = [PUSH (Word (Val "0")); PUSH (Word (Val "0")); GT] in
        let ea = Enc_consts.mk p (`User []) in
        let st = Evm_state.mk ea "" in
        let c = enc_program ea st in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: Z3.Expr.t] ~printer:Z3.Expr.to_string
          (Word.enc_int 0) (eval_stack st m (Program.length p) 0)
      );

    "1 > 0 is 1" >::(fun _ ->
        let p = [PUSH (Word (Val "0")); PUSH (Word (Val "1")); GT] in
        let ea = Enc_consts.mk p (`User []) in
        let st = Evm_state.mk ea "" in
        let c = enc_program ea st in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: Z3.Expr.t] ~printer:Z3.Expr.to_string
          (Word.enc_int 1) (eval_stack st m (Program.length p) 0)
      );

    "0 > 1 is 0" >::(fun _ ->
        let p = [PUSH (Word (Val "1")); PUSH (Word (Val "0")); GT] in
        let ea = Enc_consts.mk p (`User []) in
        let st = Evm_state.mk ea "" in
        let c = enc_program ea st in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: Z3.Expr.t] ~printer:Z3.Expr.to_string
          (Word.enc_int 0) (eval_stack st m (Program.length p) 0)
      );

    "1 > -1 is 0 (unsigned GT)" >::(fun _ ->
        let p = [PUSH (Word (Val "-1")); PUSH (Word (Val "1")); GT] in
        let ea = Enc_consts.mk p (`User []) in
        let st = Evm_state.mk ea "" in
        let c = enc_program ea st in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: Z3.Expr.t] ~printer:Z3.Expr.to_string
          (Word.enc_int 0) (eval_stack st m (Program.length p) 0)
      );

    "-1 > 1 is 1 (unsigned GT)" >::(fun _ ->
        let p = [PUSH (Word (Val "1")); PUSH (Word (Val "-1")); GT] in
        let ea = Enc_consts.mk p (`User []) in
        let st = Evm_state.mk ea "" in
        let c = enc_program ea st in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: Z3.Expr.t] ~printer:Z3.Expr.to_string
          (Word.enc_int 1) (eval_stack st m (Program.length p) 0)
      );

    (* slt *)

    "0 <_signed 0 is 0" >::(fun _ ->
        let p = [PUSH (Word (Val "0")); PUSH (Word (Val "0")); SLT] in
        let ea = Enc_consts.mk p (`User []) in
        let st = Evm_state.mk ea "" in
        let c = enc_program ea st in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: Z3.Expr.t] ~printer:Z3.Expr.to_string
          (Word.enc_int 0) (eval_stack st m (Program.length p) 0)
      );

    "1 <_signed 0 is 0" >::(fun _ ->
        let p = [PUSH (Word (Val "0")); PUSH (Word (Val "1")); SLT] in
        let ea = Enc_consts.mk p (`User []) in
        let st = Evm_state.mk ea "" in
        let c = enc_program ea st in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: Z3.Expr.t] ~printer:Z3.Expr.to_string
          (Word.enc_int 0) (eval_stack st m (Program.length p) 0)
      );

    "0 <_signed 1 is 1" >::(fun _ ->
        let p = [PUSH (Word (Val "1")); PUSH (Word (Val "0")); SLT] in
        let ea = Enc_consts.mk p (`User []) in
        let st = Evm_state.mk ea "" in
        let c = enc_program ea st in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: Z3.Expr.t] ~printer:Z3.Expr.to_string
          (Word.enc_int 1) (eval_stack st m (Program.length p) 0)
      );

    "1 <_signed -1 is 0" >::(fun _ ->
        let p = [PUSH (Word (Val "-1")); PUSH (Word (Val "1")); SLT] in
        let ea = Enc_consts.mk p (`User []) in
        let st = Evm_state.mk ea "" in
        let c = enc_program ea st in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: Z3.Expr.t] ~printer:Z3.Expr.to_string
          (Word.enc_int 0) (eval_stack st m (Program.length p) 0)
      );

    "-1 <_signed 1 is 1" >::(fun _ ->
        let p = [PUSH (Word (Val "1")); PUSH (Word (Val "-1")); SLT] in
        let ea = Enc_consts.mk p (`User []) in
        let st = Evm_state.mk ea "" in
        let c = enc_program ea st in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: Z3.Expr.t] ~printer:Z3.Expr.to_string
          (Word.enc_int 1) (eval_stack st m (Program.length p) 0)
      );

    (* sgt *)

    "0 >_signed 0 is 0" >::(fun _ ->
        let p = [PUSH (Word (Val "0")); PUSH (Word (Val "0")); SGT] in
        let ea = Enc_consts.mk p (`User []) in
        let st = Evm_state.mk ea "" in
        let c = enc_program ea st in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: Z3.Expr.t] ~printer:Z3.Expr.to_string
          (Word.enc_int 0) (eval_stack st m (Program.length p) 0)
      );

    "1 >_signed 0 is 1" >::(fun _ ->
        let p = [PUSH (Word (Val "0")); PUSH (Word (Val "1")); SGT] in
        let ea = Enc_consts.mk p (`User []) in
        let st = Evm_state.mk ea "" in
        let c = enc_program ea st in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: Z3.Expr.t] ~printer:Z3.Expr.to_string
          (Word.enc_int 1) (eval_stack st m (Program.length p) 0)
      );

    "0 >_signed 1 is 0" >::(fun _ ->
        let p = [PUSH (Word (Val "1")); PUSH (Word (Val "0")); SGT] in
        let ea = Enc_consts.mk p (`User []) in
        let st = Evm_state.mk ea "" in
        let c = enc_program ea st in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: Z3.Expr.t] ~printer:Z3.Expr.to_string
          (Word.enc_int 0) (eval_stack st m (Program.length p) 0)
      );

    "1 >_signed -1 is 1" >::(fun _ ->
        let p = [PUSH (Word (Val "-1")); PUSH (Word (Val "1")); SGT] in
        let ea = Enc_consts.mk p (`User []) in
        let st = Evm_state.mk ea "" in
        let c = enc_program ea st in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: Z3.Expr.t] ~printer:Z3.Expr.to_string
          (Word.enc_int 1) (eval_stack st m (Program.length p) 0)
      );

    "-1 >_signed 1 is 0" >::(fun _ ->
        let p = [PUSH (Word (Val "1")); PUSH (Word (Val "-1")); SGT] in
        let ea = Enc_consts.mk p (`User []) in
        let st = Evm_state.mk ea "" in
        let c = enc_program ea st in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: Z3.Expr.t] ~printer:Z3.Expr.to_string
          (Word.enc_int 0) (eval_stack st m (Program.length p) 0)
      );

    (* not *)

    "not 0b001 is 0b110" >::(fun _ ->
        let p = [PUSH (Word (Val "1")); NOT] in
        let ea = Enc_consts.mk p (`User []) in
        let st = Evm_state.mk ea "" in
        let c = enc_program ea st in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: Z3.Expr.t] ~printer:Z3.Expr.to_string
          (Word.enc_int 6) (eval_stack st m (Program.length p) 0)
      );

    "not 0b000 is 0b111" >::(fun _ ->
        let p = [PUSH (Word (Val "0")); NOT] in
        let ea = Enc_consts.mk p (`User []) in
        let st = Evm_state.mk ea "" in
        let c = enc_program ea st in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: Z3.Expr.t] ~printer:Z3.Expr.to_string
          (Word.enc_int 7) (eval_stack st m (Program.length p) 0)
      );

    "not 0b101 is 0b010" >::(fun _ ->
        let p = [PUSH (Word (Val "0b101")); NOT] in
        let ea = Enc_consts.mk p (`User []) in
        let st = Evm_state.mk ea "" in
        let c = enc_program ea st in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: Z3.Expr.t] ~printer:Z3.Expr.to_string
          (Word.enc_int 2) (eval_stack st m (Program.length p) 0)
      );

    (* push *)

    "top of the stack is the pushed word after a PUSH">:: (fun _ ->
        let p = [PUSH (Word (Val "5"))] in
        let ea = Enc_consts.mk p (`User []) in
        let st = Evm_state.mk ea "" in
        let c = enc_program ea st in
        let m = solve_model_exn [c] in
        assert_equal
          ~cmp:[%eq: Z3.Expr.t]
          ~printer:Z3.Expr.to_string
          (Word.enc_int 5)
          (eval_stack st m (Program.length p) 0)
      );

    (* number *)

    "top of the stack is some word after NUMBER" >:: (fun _ ->
        let p = [NUMBER] in
        let ea = Enc_consts.mk p (`User []) in
        let st = Evm_state.mk ea "" in
        let c = foralls (forall_vars ea) (enc_program ea st) in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: Z3.Expr.t] ~printer:Z3.Expr.to_string
          (Word.enc_int 3)
          (eval_stack ~xs:[Word.enc_int 3] st m (Program.length p) 0)
      );

    "stack after NUMBER NUMBER" >:: (fun _ ->
        let p = [NUMBER; NUMBER] in
        let ea = Enc_consts.mk p (`User []) in
        let st = Evm_state.mk ea "" in
        let c = foralls (forall_vars ea) (enc_program ea st) in
        let m = solve_model_exn [c] in
        assert_equal
          ~cmp:[%eq: Z3.Expr.t list]
          ~printer:(List.to_string ~f:(Z3.Expr.to_string))
          [Word.enc_int 3; Word.enc_int 3]
          [eval_stack ~xs:[Word.enc_int 3] st m (Program.length p) 0;
           eval_stack ~xs:[Word.enc_int 3] st m (Program.length p) 1]
      );

    (* SWAP *)

    "swap I two words on stack" >::(fun _ ->
        let p = [PUSH (Word (Val "1")); PUSH (Word (Val "2")); SWAP I] in
        let ea = Enc_consts.mk p `All in
        let st = Evm_state.mk ea "" in
        let c = enc_program ea st in
        let m = solve_model_exn [c] in
        assert_equal
          ~cmp:[%eq: Z3.Expr.t list]
          ~printer:(List.to_string ~f:Z3.Expr.to_string)
          [Word.enc_int 2; Word.enc_int 1]
          [(eval_stack st m (Program.length p) 0); (eval_stack st m (Program.length p) 1)]
      );

    "swap I with only one word" >::(fun _ ->
        let p = [PUSH (Word (Val "1")); SWAP I] in
        let ea = Enc_consts.mk p `All in
        let st = Evm_state.mk ea "" in
        (* allow to instantiate variables when evaluating model *)
        let c = foralls ea.xs (enc_program ea st) in
        let m = solve_model_exn [c] in
        assert_equal
          ~cmp:[%eq: Z3.Expr.t list]
          ~printer:(List.to_string ~f:Z3.Expr.to_string)
          [Word.enc_int 1; Word.enc_int 2]
          [(eval_stack ~xs:[Word.enc_int 2] st m (Program.length p) 0);
           (eval_stack ~xs:[Word.enc_int 2] st m (Program.length p) 1)]
      );

    "swap I with no words" >::(fun _ ->
        let p = [SWAP I] in
        let ea = Enc_consts.mk p `All in
        let st = Evm_state.mk ea "" in
        (* allow to instantiate variables when evaluating model *)
        let c = foralls ea.xs (enc_program ea st) in
        let m = solve_model_exn [c] in
        assert_equal
          ~cmp:[%eq: Z3.Expr.t list]
          ~printer:(List.to_string ~f:Z3.Expr.to_string)
          [Word.enc_int 1; Word.enc_int 2]
          [(eval_stack ~xs:[Word.enc_int 2; Word.enc_int 1] st m (Program.length p) 0);
           (eval_stack ~xs:[Word.enc_int 2; Word.enc_int 1] st m (Program.length p) 1)]
      );

     "words after swap II" >::(fun _ ->
        let p = [PUSH (Word (Val "1")); PUSH (Word (Val "2")); PUSH (Word (Val "3")); SWAP II] in
        let ea = Enc_consts.mk p (`User []) in
        let st = Evm_state.mk ea "" in
        let c = enc_program ea st in
        let m = solve_model_exn [c] in
        assert_equal
          ~cmp:[%eq: Z3.Expr.t list]
          ~printer:(List.to_string ~f:Z3.Expr.to_string)
          [Word.enc_int 3; Word.enc_int 2; Word.enc_int 1]
          [eval_stack st m (Program.length p) 0;
           eval_stack st m (Program.length p) 1;
           eval_stack st m (Program.length p) 2;]
      );

     "preserve words between swap III" >::(fun _ ->
        let p = [PUSH (Word (Val "1")); PUSH (Word (Val "2")); PUSH (Word (Val "3")); PUSH (Word (Val "4")); SWAP III] in
        let ea = Enc_consts.mk p (`User []) in
        let st = Evm_state.mk ea "" in
        let c = enc_program ea st in
        let m = solve_model_exn [c] in
        assert_equal
          ~cmp:[%eq: Z3.Expr.t list]
          ~printer:(List.to_string ~f:Z3.Expr.to_string)
          [Word.enc_int 2; Word.enc_int 3]
          [eval_stack st m (Program.length p) 1;
           eval_stack st m (Program.length p) 2;]
      );

    (* dup *)

    "duplicate top word" >:: (fun _ ->
        let p = [PUSH (Word (Val "1")); DUP I] in
        let ea = Enc_consts.mk p (`User []) in
        let st = Evm_state.mk ea "" in
        let c = enc_program ea st in
        let m = solve_model_exn [c] in
        assert_equal
          ~cmp:[%eq: Z3.Expr.t list]
          ~printer:(List.to_string ~f:Z3.Expr.to_string)
          [Word.enc_int 1; Word.enc_int 1]
          [eval_stack st m (Program.length p) 0;
           eval_stack st m (Program.length p) 1;]
      );

    "DUP I with no words" >::(fun _ ->
        let p = [DUP I] in
        let ea = Enc_consts.mk p `All in
        let st = Evm_state.mk ea "" in
        (* allow to instantiate variables when evaluating model *)
        let c = foralls ea.xs (enc_program ea st) in
        let m = solve_model_exn [c] in
        assert_equal
          ~cmp:[%eq: Z3.Expr.t list]
          ~printer:(List.to_string ~f:Z3.Expr.to_string)
          [Word.enc_int 1; Word.enc_int 1]
          [(eval_stack ~xs:[Word.enc_int 1] st m (Program.length p) 0);
           (eval_stack ~xs:[Word.enc_int 1] st m (Program.length p) 1)]
      );
  ] @
  (List.map all_of_idx ~f:(fun idx ->
       "effect of DUP " ^ show_idx idx >:: (fun _ ->
           let i = idx_to_enum idx in
           let ip = List.init i ~f:(fun n -> PUSH (val_of_int_safe n)) in
           let p = ip @ [DUP idx] in
           let ea = Enc_consts.mk p (`User []) in
           let st = Evm_state.mk ea "" in
           let c = enc_program ea st in
           let m = solve_model_exn [c] in
           assert_equal ~cmp:[%eq: Z3.Expr.t] ~printer:Z3.Expr.to_string
             (eval_stack st m (Program.length p) i)
             (eval_stack st m (Program.length p) 0)
         ))) @
  (List.map all_of_idx ~f:(fun idx ->
       "preservation of words between DUP " ^ show_idx idx >:: (fun _ ->
           let i = idx_to_enum idx in
           let ip = List.init i ~f:(fun n -> PUSH (val_of_int_safe n)) in
           let p = ip @ [DUP idx] in
           let ea = Enc_consts.mk p (`User []) in
           let st = Evm_state.mk ea "" in
           let c = enc_program ea st in
           let m = solve_model_exn [c] in
           assert_equal
             ~cmp:[%eq: Z3.Expr.t list]
             ~printer:(List.to_string ~f:Z3.Expr.to_string)
             (List.init (i - 1) ~f:(fun k -> (eval_stack st m (Program.length p) (k + 1))))
             (List.init (i - 1) ~f:(fun k -> (eval_stack st m (Program.length ip) (k + 1))))
         )))

let pres_stack =
  (* test preservation of words for all opcodes *)
  List.map (Instruction.encodable @ Instruction.constant_uninterpreted)
    ~f:(fun oc -> "preservation of words by " ^ [%show: Instruction.t] oc
                  >:: (fun _ -> test_stack_pres oc))

let stack_ctr =
  (* test all instructions manipulate stack counter correctly *)
  List.map (Instruction.encodable @ Instruction.constant_uninterpreted)
    ~f:(fun oc -> "stack_ctr is changed correctly by " ^ [%show: Instruction.t] oc
                  >:: (fun _ -> test_stack_ctr [oc])) @
  [
    "test a program leading to an empty stack">:: (fun _ ->
        test_stack_ctr [PUSH (Word (Val "1")); PUSH (Word (Val "1")); ADD; POP]
      );

    "test stack counter for empty program">:: (fun _ ->
        test_stack_ctr []
      );
  ]

let exc_halt =
  (* test all instructions preserve exceptional halting *)
  List.map (Instruction.encodable @ Instruction.constant_uninterpreted)
    ~f:(fun oc -> "exc_halt is preserved by " ^ [%show: Instruction.t] oc
                  >:: (fun _ -> test_exc_halt_pres [oc])) @
  (* test no exceptional halting due to stack underflow *)
  List.map (Instruction.encodable @ Instruction.constant_uninterpreted)
    ~f:(fun oc -> "no exc_halt due to stack underflow by "  ^ [%show: Instruction.t] oc
                  >:: (fun _ -> test_no_exc_halt [oc])) @
  [
    "valid program does not halt exceptionally">:: (fun _ ->
        test_no_exc_halt [ADD; SUB]
      );

    "PUSHing too many words leads to a stack overflow">:: (fun _ ->
        let max = Int.pow 2 !SI.size in
        let p = List.init max ~f:(fun _ -> PUSH (Word (Val "1"))) in
        let ea = Enc_consts.mk p (`User []) in
        let st = Evm_state.mk ea "" in
        let c = enc_program ea st in
        let m = solve_model_exn [c] in
        assert_equal
          ~cmp:[%eq: Z3.Expr.t]
          ~printer:Z3.Expr.to_string
          top
          (eval_exc_halt st m (Program.length p))
      );

    "exceptional halt persists for multiple instructions">:: (fun _ ->
        test_exc_halt_pres [SUB; PUSH (Word (Val "3"))]
      );
  ]

let forced_stack_underflow =
  (* test below use hack to erase xs to start from emtpy stack *)
  [
    "add with only one word">:: (fun _ ->
        let p = [PUSH (Word (Val "3")); ADD] in
        let ea = Enc_consts.mk p (`User []) in
        let st = Evm_state.mk {ea with p = []} "" in
        let c =
          init {ea with p = []} st <&>
          enc_instruction ea st (num Z.zero) (List.nth_exn p 0) <&>
          enc_instruction ea st (num Z.one) (List.nth_exn p 1)
        in
        let m = solve_model_exn [c] in
        assert_equal
          ~cmp:[%eq: Z3.Expr.t]
          ~printer:Z3.Expr.to_string
          top
          (eval_exc_halt st m (Program.length p))
      );

    "add with empty stack">:: (fun _ ->
        let p = [ADD] in
        let ea = Enc_consts.mk p (`User []) in
        let st = Evm_state.mk {ea with p = []} "" in
        let c = init {ea with p = []} st <&>
                enc_instruction ea st (num Z.zero) ADD in
        let m = solve_model_exn [c] in
        assert_equal
          ~cmp:[%eq: Z3.Expr.t]
          ~printer:Z3.Expr.to_string
          top
          (eval_exc_halt st m (Program.length p))
      );

    "SUB with only one word">:: (fun _ ->
        let p = [PUSH (Word (Val "3")); SUB] in
        let ea = Enc_consts.mk p (`User []) in
        let st = Evm_state.mk {ea with p = []} "" in
        let c =
          init {ea with p = []} st <&>
          enc_instruction ea st (num Z.zero) (List.nth_exn p 0) <&>
          enc_instruction ea st (num Z.one) (List.nth_exn p 1)
        in
        let m = solve_model_exn [c] in
        assert_equal
          ~cmp:[%eq: Z3.Expr.t]
          ~printer:Z3.Expr.to_string
          top
          (eval_exc_halt st m (Program.length p))
      );

    "sub with empty stack">:: (fun _ ->
        let p = [SUB] in
        let ea = Enc_consts.mk p (`User []) in
        let st = Evm_state.mk {ea with p = []} "" in
        let c =
          init {ea with p = []} st <&>
          enc_instruction ea st (num Z.zero) (List.nth_exn p 0)
        in
        let m = solve_model_exn [c] in
        assert_equal
          ~cmp:[%eq: Z3.Expr.t]
          ~printer:Z3.Expr.to_string
          top
          (eval_exc_halt st m (Program.length p))
      );

    "pop on empty stack leads to stack underflow" >:: (fun _ ->
        let p = [POP] in
        let ea = Enc_consts.mk p (`User []) in
        let st = Evm_state.mk {ea with p = []} "" in
        let c =
          init {ea with p = []} st <&>
          enc_instruction ea st (num Z.zero) (List.nth_exn p 0)
        in
        let m = solve_model_exn [c] in
        assert_equal
          ~cmp:[%eq: Z3.Expr.t]
          ~printer:Z3.Expr.to_string
          top
          (eval_exc_halt st m (Program.length p))
      );
  ]

let gas_cost =
  [
    "after 0 instruction no gas has been used">::(fun _ ->
        let ea = Enc_consts.mk [] (`User []) in
        let st = Evm_state.mk ea "" in
        let c = init ea st in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: GC.t] ~printer:[%show: GC.t]
          GC.zero
          (eval_gas st m (PC.of_int 0))
      );

    "after some instruction some gas has been used">::(fun _ ->
        let p = [PUSH (Word (Val "6")); PUSH (Word (Val "2")); ADD] in
        let ea = Enc_consts.mk p (`User []) in
        let st = Evm_state.mk ea "" in
        let c = enc_program ea st in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: GC.t] ~printer:[%show: GC.t]
          (total_gas_cost p)
          (eval_gas st m (Program.length p))
      );
  ]

let misc =
  [
    (* init *)

    "model of the initial stack holds 0 for every stack address">:: (fun _ ->
        let ea = Enc_consts.mk [] (`User []) in
        let st = Evm_state.mk ea "" in
        let c = init ea st in
        let m = solve_model_exn [c] in
        let sk_size = (Int.pow 2 !SI.size) - 1 in
        assert_equal
          ~cmp:[%eq: Z3.Expr.t list]
          ~printer:(List.to_string ~f:Z3.Expr.to_string)
          (List.init sk_size ~f:(fun _ -> Word.enc_int 0))
          (List.init sk_size ~f:(eval_stack st m (PC.of_int 0)))
      );

    (* init balance *)

    "inital balance for arg in range">:: (fun _ ->
        let ea = Enc_consts.mk [PUSH (Word (Val "2")); BALANCE] (`User []) in
        let st = Evm_state.mk ea "" in
        let c = foralls (forall_vars ea) (enc_program ea st) in
        let i = Word.enc_int 3 in (* set for all quantified variable to 3 for test *)
        let m = solve_model_exn [c] in
        let brom = Map.find_exn ea.roms BALANCE in
        assert_equal
          ~cmp:[%eq: Z3.Expr.t]
          ~printer:Z3.Expr.to_string
          i
          (Z3util.eval_func_decl m brom ([i] @ [Word.enc_int 2]))
      );

    "initial balance for given args not in range">:: (fun _ ->
        let ea = Enc_consts.mk [PUSH (Word (Val "2")); BALANCE] (`User []) in
        let st = Evm_state.mk ea "" in
        let c = foralls (forall_vars ea) (enc_program ea st) in
        let m = solve_model_exn [c] in
        let brom = Map.find_exn ea.roms BALANCE in
        let ias = [0; 1; 3] in (* not 2, as this is the argument of BALANCE *)
        assert_equal ~cmp:[%eq: Z3.Expr.t list] ~printer:(List.to_string ~f:Z3.Expr.to_string)
          [Word.enc_int 0; Word.enc_int 0; Word.enc_int 0] (* return default value 0 *)
          (List.map ias ~f:(fun ia -> Z3util.eval_func_decl m brom (forall_vars ea @ [Word.enc_int ia])))
      );

    "inital balance for computed arg in range">:: (fun _ ->
        let ea = Enc_consts.mk [PUSH (Word (Val "1")); PUSH (Word (Val "1")); ADD; BALANCE] (`User []) in
        let st = Evm_state.mk ea "" in
        let c = foralls (forall_vars ea) (enc_program ea st) in
        let i = Word.enc_int 3 in (* set for all quantified variable to 3 for test *)
        let m = solve_model_exn [c] in
        let brom = Map.find_exn ea.roms BALANCE in
        assert_equal
          ~cmp:[%eq: Z3.Expr.t]
          ~printer:Z3.Expr.to_string
          i
          (Z3util.eval_func_decl m brom ([i] @ [Word.enc_int 2]))
      );

    "initial balance for computed arg where given args are not in range">:: (fun _ ->
        let ea = Enc_consts.mk [PUSH (Word (Val "1")); PUSH (Word (Val "1")); ADD; BALANCE] (`User []) in
        let st = Evm_state.mk ea "" in
        let c = foralls (forall_vars ea) (enc_program ea st) in
        let m = solve_model_exn [c] in
        let ias = [0; 1; 3] in (* not 2, as this is the argument of BALANCE *)
        let brom = Map.find_exn ea.roms BALANCE in
        assert_equal ~cmp:[%eq: Z3.Expr.t list] ~printer:(List.to_string ~f:Z3.Expr.to_string)
          [Word.enc_int 0; Word.enc_int 0; Word.enc_int 0] (* return default value 0 *)
          (List.map ias ~f:(fun ia -> Z3util.eval_func_decl m brom (forall_vars ea @ [Word.enc_int ia])))
      );

    (* mk_uint_vars *)

    "ADD does not generate variables">:: (fun _ ->
        let p = [ADD] in
        let ea = Enc_consts.mk p `All in
        assert_bool "Some entry for ADD is found" (Option.is_none (Map.find ea.uis ADD))
      );

    "[NUMBER] generates one variable">:: (fun _ ->
        let p = [NUMBER] in
        let ea = Enc_consts.mk p `All in
        assert_equal ~cmp:[%eq: Z3.Expr.t list] ~printer:(List.to_string ~f:Z3.Expr.to_string)
          [(Word.const "x_NUMBER")] (Option.value_exn (Map.find ea.uis NUMBER))
      );

    "[NUMBER; NUMBER] generates one variable">:: (fun _ ->
        let p = [NUMBER; NUMBER] in
        let ea = Enc_consts.mk p `All in
        assert_equal ~cmp:[%eq: Z3.Expr.t list] ~printer:(List.to_string ~f:Z3.Expr.to_string)
          [(Word.const "x_NUMBER")] (Option.value_exn (Map.find ea.uis NUMBER))
      );

    "[BALANCE] generates one variable">:: (fun _ ->
        let p = [BALANCE] in
        let ea = Enc_consts.mk p `All in
        assert_equal ~cmp:[%eq: Z3.Expr.t list] ~printer:(List.to_string ~f:Z3.Expr.to_string)
          [(Word.const "x_BALANCE_0")] (Option.value_exn (Map.find ea.uis BALANCE))
      );

    "[BALANCE; BALANCE] generates two variables">:: (fun _ ->
        let p = [BALANCE; BALANCE] in
        let ea = Enc_consts.mk p `All in
        assert_equal ~cmp:[%eq: Z3.Expr.t list] ~printer:(List.to_string ~f:Z3.Expr.to_string)
          [(Word.const "x_BALANCE_0"); (Word.const "x_BALANCE_1")] (Option.value_exn (Map.find ea.uis BALANCE))
      );

    (* mk_unint_fun *)

    "ADD does not generate function">:: (fun _ ->
        let p = [ADD;] in
        let ea = Enc_consts.mk p `All in
        assert_bool "No entry for ADD is found" (Option.is_none (Map.find ea.roms ADD))
      );

    "NUMBER does not generate function">:: (fun _ ->
        let p = [ADD;] in
        let ea = Enc_consts.mk p `All in
        assert_bool "No entry for NUMBER is found" (Option.is_none (Map.find ea.roms NUMBER))
      );

    "[BALANCE] generates one function">:: (fun _ ->
        let p = [BALANCE] in
        let ea = Enc_consts.mk p `All in
        let f = Option.value_exn (Map.find ea.roms BALANCE) in
        assert_equal ~cmp:[%eq: string * int] ~printer:[%show: string * int]
          ("f_BALANCE", 3) (Z3.Symbol.to_string (Z3.FuncDecl.get_name f), Z3.FuncDecl.get_arity f)
      );

    "[BALANCE; BALANCE] generates one function">:: (fun _ ->
        let p = [BALANCE; BALANCE] in
        let ea = Enc_consts.mk p `All in
        let f = Option.value_exn (Map.find ea.roms BALANCE) in
        assert_equal ~cmp:[%eq: string * int] ~printer:[%show: string * int]
          ("f_BALANCE", 4) (Z3.Symbol.to_string (Z3.FuncDecl.get_name f), Z3.FuncDecl.get_arity f)
      );

    "[BALANCE; BLOCKHASH] generate function for BALANCE">:: (fun _ ->
        let p = [BALANCE; BLOCKHASH] in
        let ea = Enc_consts.mk p `All in
        let f = Option.value_exn (Map.find ea.roms BALANCE) in
        assert_equal ~cmp:[%eq: string * int] ~printer:[%show: string * int]
          ("f_BALANCE", 4) (Z3.Symbol.to_string (Z3.FuncDecl.get_name f), Z3.FuncDecl.get_arity f)
      );

    "[BALANCE; BLOCKHASH] generate function for BLOCKHASH">:: (fun _ ->
        let p = [BALANCE; BLOCKHASH] in
        let ea = Enc_consts.mk p `All in
        let f = Option.value_exn (Map.find ea.roms BLOCKHASH) in
        assert_equal ~cmp:[%eq: string * int] ~printer:[%show: string * int]
          ("f_BLOCKHASH", 4) (Z3.Symbol.to_string (Z3.FuncDecl.get_name f), Z3.FuncDecl.get_arity f)
      );

    "[EXP] generates one function">:: (fun _ ->
        let p = [EXP] in
        let ea = Enc_consts.mk p `All in
        let f = Option.value_exn (Map.find ea.roms EXP) in
        assert_equal ~cmp:[%eq: string * int] ~printer:[%show: string * int]
          ("f_EXP", 5) (Z3.Symbol.to_string (Z3.FuncDecl.get_name f), Z3.FuncDecl.get_arity f)
      );

    (* mk_store_vars *)

    "For ADD no variable is generated">:: (fun _ ->
        let p = [ADD] in
        let ea = Enc_consts.mk p `All in
        assert_equal ~cmp:[%eq: Z3.Expr.t list] ~printer:(List.to_string ~f:Z3.Expr.to_string)
          [] ea.ss
      );

    "For SSTORE one variable is generated">:: (fun _ ->
        let p = [SSTORE] in
        let ea = Enc_consts.mk p `All in
        assert_equal ~cmp:[%eq: Z3.Expr.t list] ~printer:(List.to_string ~f:Z3.Expr.to_string)
          [(Word.const "x_SSTORE_0")] ea.ss
      );

    "[SLOAD] generates one variable">:: (fun _ ->
        let p = [PUSH (Word (Val "1")); SLOAD;] in
        let ea = Enc_consts.mk p `All in
        assert_equal ~cmp:[%eq: Z3.Expr.t list] ~printer:(List.to_string ~f:Z3.Expr.to_string)
          [(Word.const "x_SLOAD_0")] ea.ss
      );

    "Two SLOADs generate two variables">:: (fun _ ->
        let p = [PUSH (Word (Val "1")); SLOAD; PUSH (Word (Val "2")); PUSH (Word (Val "1")); SLOAD;] in
        let ea = Enc_consts.mk p `All in
        assert_equal ~cmp:[%eq: Z3.Expr.t list] ~printer:(List.to_string ~f:Z3.Expr.to_string)
          [(Word.const "x_SLOAD_0"); (Word.const "x_SLOAD_1")] ea.ss
    );
]

let suite =
  (* set low for fast testing *)
  Word.set_wsz 3; SI.set_sas 6;
  "suite" >:::
  effect @ pres_stack @ stack_ctr @ exc_halt @ forced_stack_underflow
  @ gas_cost @ misc

let () =
  run_test_tt_main suite
