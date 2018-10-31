open Core
open OUnit2
open Z3util
open Instruction
open Program
open Evmenc

(* set low for fast testing *)
let ses = 3 and sas = 6

let test_stack_pres oc =
  let (d, _) = delta_alpha oc in
  (* create program that initializes stack with d + 2 values *)
  let ip = List.init (d + 2) ~f:(fun i -> PUSH (Val (Int.to_string i))) in
  let p = ip @ [oc] in
  let ea = mk_enc_consts p (`User []) in
  let st = mk_state ea "" in
  let c = enc_program ea st in
  let m = solve_model_exn [c] in
  (* check all elements below delta *)
  assert_equal ~cmp:[%eq: Z3.Expr.t list]
    ~printer:(List.to_string ~f:Z3.Expr.to_string)
    [(senum 0); (senum 1)]
    [(eval_stack st m (List.length p) 0); (eval_stack st m (List.length p) 1)]

let test_stack_ctr p =
  let d = stack_depth p in
  (* create program that initializes stack with d values *)
  let ip = List.init d ~f:(fun i -> PUSH (Val (Int.to_string i))) in
  let p = ip @ p in
  let ea = mk_enc_consts p (`User []) in
  let st = mk_state ea "" in
  let c = enc_program ea st in
  let m = solve_model_exn [c] in
  let upd_sc sc oc = let (d, a) = delta_alpha oc in sc - d + a in
  (* check that stack counter is adjusted accordingly *)
  assert_equal ~cmp:[%eq: Z3.Expr.t] ~printer:Z3.Expr.to_string
    (sanum (List.fold_left p ~init:0 ~f:upd_sc))
    (eval_stack_ctr st m (List.length p))

let test_no_exc_halt p =
  let d = stack_depth p in
  (* create program that initializes stack with d values *)
  let ip = List.init d ~f:(fun i -> PUSH (Val (Int.to_string i))) in
  let p = ip @ p in
  let ea = mk_enc_consts p (`User []) in
  let st = mk_state ea "" in
  let c = enc_program ea st in
  let m = solve_model_exn [c] in
  (* check no exceptional halting occured *)
  assert_equal ~cmp:[%eq: Z3.Expr.t] ~printer:Z3.Expr.to_string
    btm
    (eval_exc_halt st m (List.length p))

let test_exc_halt_pres p =
  let max = Int.pow 2 sas in
  let ip = List.init max ~f:(fun _ -> PUSH (Val "1")) in
  let p = ip @ p in
  let ea = mk_enc_consts p (`User []) in
  let st = mk_state ea "" in
  let c = enc_program ea st in
  let m = solve_model_exn [c] in
  assert_equal
    ~cmp:[%eq: Z3.Expr.t]
    ~printer:Z3.Expr.to_string
    top
    (eval_exc_halt st m (List.length p))

let effect =
  [
    (* add *)

    "add two elements on the stack">:: (fun _ ->
        let p = [PUSH (Val "4"); PUSH (Val "5"); ADD] in
        let ea = mk_enc_consts p (`User []) in
        let st = mk_state ea "" in
        let c = enc_program ea st in
        let m = solve_model_exn [c] in
        assert_equal
          ~cmp:[%eq: Z3.Expr.t]
          ~printer:Z3.Expr.to_string
          (senum 9)
          (eval_stack st m (List.length p) 0)
      );

    (* sub *)

    "subtract two elements on the stack">:: (fun _ ->
        let p = [PUSH (Val "3"); PUSH (Val "8"); SUB] in
        let ea = mk_enc_consts p (`User []) in
        let st = mk_state ea "" in
        let c = enc_program ea st in
        let m = solve_model_exn [c] in
        assert_equal
          ~cmp:[%eq: Z3.Expr.t]
          ~printer:Z3.Expr.to_string
          (senum 5)
          (eval_stack st m (List.length p) 0)
      );

    "subtract two elements on the stack with negative result">:: (fun _ ->
        let p = [PUSH (Val "13"); PUSH (Val "8"); SUB] in
        let ea = mk_enc_consts p (`User []) in
        let st = mk_state ea "" in
        let c = enc_program ea st in
        let m = solve_model_exn [c] in
        assert_equal
          ~cmp:[%eq: Z3.Expr.t]
          ~printer:Z3.Expr.to_string
          (senum (-5))
          (eval_stack st m (List.length p) 0)
      );

    (* add and sub *)

    "combine add and sub">:: (fun _ ->
        let p = [PUSH (Val "3"); PUSH (Val "2"); PUSH (Val "2"); ADD; SUB] in
        let ea = mk_enc_consts p (`User []) in
        let st = mk_state ea "" in
        let c = enc_program ea st in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: Z3.Expr.t] ~printer:Z3.Expr.to_string
          (senum 1) (eval_stack st m (List.length p) 0)
      );

    (* div *)

    "divide 1 by 1" >::(fun _ ->
        let p = [PUSH (Val "1"); PUSH (Val "1"); DIV] in
        let ea = mk_enc_consts p (`User []) in
        let st = mk_state ea "" in
        let c = enc_program ea st in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: Z3.Expr.t] ~printer:Z3.Expr.to_string
          (senum 1) (eval_stack st m (List.length p) 0)
      );

    "divide 4 by 2" >::(fun _ ->
        let p = [PUSH (Val "2"); PUSH (Val "4"); DIV] in
        let ea = mk_enc_consts p (`User []) in
        let st = mk_state ea "" in
        let c = enc_program ea st in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: Z3.Expr.t] ~printer:Z3.Expr.to_string
          (senum 2) (eval_stack st m (List.length p) 0)
      );

    "divide 5 by 2" >::(fun _ ->
        let p = [PUSH (Val "2"); PUSH (Val "5"); DIV] in
        let ea = mk_enc_consts p (`User []) in
        let st = mk_state ea "" in
        let c = enc_program ea st in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: Z3.Expr.t] ~printer:Z3.Expr.to_string
          (senum 2) (eval_stack st m (List.length p) 0)
      );

    "divide 2 by 4" >::(fun _ ->
        let p = [PUSH (Val "4"); PUSH (Val "2"); DIV] in
        let ea = mk_enc_consts p (`User []) in
        let st = mk_state ea "" in
        let c = enc_program ea st in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: Z3.Expr.t] ~printer:Z3.Expr.to_string
          (senum 0) (eval_stack st m (List.length p) 0)
      );

    "divide 2 by 0" >::(fun _ ->
        let p = [PUSH (Val "0"); PUSH (Val "2"); DIV] in
        let ea = mk_enc_consts p (`User []) in
        let st = mk_state ea "" in
        let c = enc_program ea st in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: Z3.Expr.t] ~printer:Z3.Expr.to_string
          (senum 0) (eval_stack st m (List.length p) 0)
      );

    "divide 0 by 0" >::(fun _ ->
        let p = [PUSH (Val "0"); PUSH (Val "0"); DIV] in
        let ea = mk_enc_consts p (`User []) in
        let st = mk_state ea "" in
        let c = enc_program ea st in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: Z3.Expr.t] ~printer:Z3.Expr.to_string
          (senum 0) (eval_stack st m (List.length p) 0)
      );

    (* mod *)

    "2 modulo 1" >::(fun _ ->
        let p = [PUSH (Val "1"); PUSH (Val "2"); MOD] in
        let ea = mk_enc_consts p (`User []) in
        let st = mk_state ea "" in
        let c = enc_program ea st in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: Z3.Expr.t] ~printer:Z3.Expr.to_string
          (senum 0) (eval_stack st m (List.length p) 0)
      );

    "4 modulo 2" >::(fun _ ->
        let p = [PUSH (Val "2"); PUSH (Val "4"); MOD] in
        let ea = mk_enc_consts p (`User []) in
        let st = mk_state ea "" in
        let c = enc_program ea st in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: Z3.Expr.t] ~printer:Z3.Expr.to_string
          (senum 0) (eval_stack st m (List.length p) 0)
      );

    "5 modulo 2" >::(fun _ ->
        let p = [PUSH (Val "2"); PUSH (Val "5"); MOD] in
        let ea = mk_enc_consts p (`User []) in
        let st = mk_state ea "" in
        let c = enc_program ea st in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: Z3.Expr.t] ~printer:Z3.Expr.to_string
          (senum 1) (eval_stack st m (List.length p) 0)
      );

    "2 modulo 4" >::(fun _ ->
        let p = [PUSH (Val "4"); PUSH (Val "2"); MOD] in
        let ea = mk_enc_consts p (`User []) in
        let st = mk_state ea "" in
        let c = enc_program ea st in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: Z3.Expr.t] ~printer:Z3.Expr.to_string
          (senum 2) (eval_stack st m (List.length p) 0)
      );

    "2 modulo 0" >::(fun _ ->
        let p = [PUSH (Val "0"); PUSH (Val "2"); MOD] in
        let ea = mk_enc_consts p (`User []) in
        let st = mk_state ea "" in
        let c = enc_program ea st in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: Z3.Expr.t] ~printer:Z3.Expr.to_string
          (senum 0) (eval_stack st m (List.length p) 0)
      );

    "0 modulo 0" >::(fun _ ->
        let p = [PUSH (Val "0"); PUSH (Val "0"); MOD] in
        let ea = mk_enc_consts p (`User []) in
        let st = mk_state ea "" in
        let c = enc_program ea st in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: Z3.Expr.t] ~printer:Z3.Expr.to_string
          (senum 0) (eval_stack st m (List.length p) 0)
      );

    (* addmod *)

    "(2 + 1) mod 2 = 1" >::(fun _ ->
        let p = [PUSH (Val "2"); PUSH (Val "1"); PUSH (Val "2"); ADDMOD] in
        let ea = mk_enc_consts p (`User []) in
        let st = mk_state ea "" in
        let c = enc_program ea st in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: Z3.Expr.t] ~printer:Z3.Expr.to_string
          (senum 1) (eval_stack st m (List.length p) 0)
      );

    "(7 + 1) mod 3 = 2 (overflow which should be ignored)" >::(fun _ ->
        let p = [PUSH (Val "3"); PUSH (Val "1"); PUSH (Val "7"); ADDMOD] in
        let ea = mk_enc_consts p (`User []) in
        let st = mk_state ea "" in
        let c = enc_program ea st in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: Z3.Expr.t] ~printer:Z3.Expr.to_string
          (senum 2) (eval_stack st m (List.length p) 0)
      );

    "(1 + 1) mod 3 = 2" >::(fun _ ->
        let p = [PUSH (Val "3"); PUSH (Val "1"); PUSH (Val "1"); ADDMOD] in
        let ea = mk_enc_consts p (`User []) in
        let st = mk_state ea "" in
        let c = enc_program ea st in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: Z3.Expr.t] ~printer:Z3.Expr.to_string
          (senum 2) (eval_stack st m (List.length p) 0)
      );

    "(1 + 1) mod 2 = 0" >::(fun _ ->
        let p = [PUSH (Val "2"); PUSH (Val "1"); PUSH (Val "1"); ADDMOD] in
        let ea = mk_enc_consts p (`User []) in
        let st = mk_state ea "" in
        let c = enc_program ea st in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: Z3.Expr.t] ~printer:Z3.Expr.to_string
          (senum 0) (eval_stack st m (List.length p) 0)
      );

    "(0 + 1) mod 0 = 0" >::(fun _ ->
        let p = [PUSH (Val "0"); PUSH (Val "1"); PUSH (Val "0"); ADDMOD] in
        let ea = mk_enc_consts p (`User []) in
        let st = mk_state ea "" in
        let c = enc_program ea st in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: Z3.Expr.t] ~printer:Z3.Expr.to_string
          (senum 0) (eval_stack st m (List.length p) 0)
      );

    "(7 + 1) mod 2 = 0 (overflow which should be ignored)" >::(fun _ ->
        let p = [PUSH (Val "2"); PUSH (Val "1"); PUSH (Val "7"); ADDMOD] in
        let ea = mk_enc_consts p (`User []) in
        let st = mk_state ea "" in
        let c = enc_program ea st in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: Z3.Expr.t] ~printer:Z3.Expr.to_string
          (senum 0) (eval_stack st m (List.length p) 0)
      );

    "(-1 + 1) mod 2 = 0" >::(fun _ ->
        let p = [PUSH (Val "2"); PUSH (Val "1"); PUSH (Val "-1"); ADDMOD] in
        let ea = mk_enc_consts p (`User []) in
        let st = mk_state ea "" in
        let c = enc_program ea st in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: Z3.Expr.t] ~printer:Z3.Expr.to_string
          (senum 0) (eval_stack st m (List.length p) 0)
      );

    (* iszero *)

    "0 iszero is true" >::(fun _ ->
        let p = [PUSH (Val "0"); ISZERO] in
        let ea = mk_enc_consts p (`User []) in
        let st = mk_state ea "" in
        let c = enc_program ea st in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: Z3.Expr.t] ~printer:Z3.Expr.to_string
          (senum 1) (eval_stack st m (List.length p) 0)
      );

    "1 iszero is false" >::(fun _ ->
        let p = [PUSH (Val "1"); ISZERO] in
        let ea = mk_enc_consts p (`User []) in
        let st = mk_state ea "" in
        let c = enc_program ea st in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: Z3.Expr.t] ~printer:Z3.Expr.to_string
          (senum 0) (eval_stack st m (List.length p) 0)
      );

    "0 - 5 iszero is false" >::(fun _ ->
        let p = [PUSH (Val "5"); PUSH (Val "0"); SUB; ISZERO] in
        let ea = mk_enc_consts p (`User []) in
        let st = mk_state ea "" in
        let c = enc_program ea st in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: Z3.Expr.t] ~printer:Z3.Expr.to_string
          (senum 0) (eval_stack st m (List.length p) 0)
      );

    (* and *)

    "0 & 1 is 0" >::(fun _ ->
        let p = [PUSH (Val "1"); PUSH (Val "0"); AND] in
        let ea = mk_enc_consts p (`User []) in
        let st = mk_state ea "" in
        let c = enc_program ea st in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: Z3.Expr.t] ~printer:Z3.Expr.to_string
          (senum 0) (eval_stack st m (List.length p) 0)
      );

    "1 & 1 is 1" >::(fun _ ->
        let p = [PUSH (Val "1"); PUSH (Val "1"); AND] in
        let ea = mk_enc_consts p (`User []) in
        let st = mk_state ea "" in
        let c = enc_program ea st in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: Z3.Expr.t] ~printer:Z3.Expr.to_string
          (senum 1) (eval_stack st m (List.length p) 0)
      );

    "0 & 0 is 0" >::(fun _ ->
        let p = [PUSH (Val "0"); PUSH (Val "0"); AND] in
        let ea = mk_enc_consts p (`User []) in
        let st = mk_state ea "" in
        let c = enc_program ea st in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: Z3.Expr.t] ~printer:Z3.Expr.to_string
          (senum 0) (eval_stack st m (List.length p) 0)
      );

    "1 & 0 is 0" >::(fun _ ->
        let p = [PUSH (Val "1"); PUSH (Val "0"); AND] in
        let ea = mk_enc_consts p (`User []) in
        let st = mk_state ea "" in
        let c = enc_program ea st in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: Z3.Expr.t] ~printer:Z3.Expr.to_string
          (senum 0) (eval_stack st m (List.length p) 0)
      );

    "AND is idempotent (0b101)" >::(fun _ ->
        let p = [PUSH (Val "0b101"); PUSH (Val "0b101"); AND] in
        let ea = mk_enc_consts p (`User []) in
        let st = mk_state ea "" in
        let c = enc_program ea st in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: Z3.Expr.t] ~printer:Z3.Expr.to_string
          (senum 5) (eval_stack st m (List.length p) 0)
      );

    "0b111 & 0b100 is 0b100" >::(fun _ ->
        let p = [PUSH (Val "0b111"); PUSH (Val "0b100"); AND] in
        let ea = mk_enc_consts p (`User []) in
        let st = mk_state ea "" in
        let c = enc_program ea st in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: Z3.Expr.t] ~printer:Z3.Expr.to_string
          (senum 4) (eval_stack st m (List.length p) 0)
      );

    (* or *)

    "0 | 1 is 1" >::(fun _ ->
        let p = [PUSH (Val "0"); PUSH (Val "1"); OR] in
        let ea = mk_enc_consts p (`User []) in
        let st = mk_state ea "" in
        let c = enc_program ea st in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: Z3.Expr.t] ~printer:Z3.Expr.to_string
          (senum 1) (eval_stack st m (List.length p) 0)
      );

    "1 | 1 is 1" >::(fun _ ->
        let p = [PUSH (Val "1"); PUSH (Val "1"); OR] in
        let ea = mk_enc_consts p (`User []) in
        let st = mk_state ea "" in
        let c = enc_program ea st in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: Z3.Expr.t] ~printer:Z3.Expr.to_string
          (senum 1) (eval_stack st m (List.length p) 0)
      );

    "0 | 0 is 0" >::(fun _ ->
        let p = [PUSH (Val "0"); PUSH (Val "0"); OR] in
        let ea = mk_enc_consts p (`User []) in
        let st = mk_state ea "" in
        let c = enc_program ea st in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: Z3.Expr.t] ~printer:Z3.Expr.to_string
          (senum 0) (eval_stack st m (List.length p) 0)
      );

    "1 | 0 is 1" >::(fun _ ->
        let p = [PUSH (Val "1"); PUSH (Val "0"); OR] in
        let ea = mk_enc_consts p (`User []) in
        let st = mk_state ea "" in
        let c = enc_program ea st in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: Z3.Expr.t] ~printer:Z3.Expr.to_string
          (senum 1) (eval_stack st m (List.length p) 0)
      );

    "OR is idempotent (0b101)" >::(fun _ ->
        let p = [PUSH (Val "0b101"); PUSH (Val "0b101"); OR] in
        let ea = mk_enc_consts p (`User []) in
        let st = mk_state ea "" in
        let c = enc_program ea st in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: Z3.Expr.t] ~printer:Z3.Expr.to_string
          (senum 5) (eval_stack st m (List.length p) 0)
      );

    "0b001 | 0b100 is 0b101" >::(fun _ ->
        let p = [PUSH (Val "0b001"); PUSH (Val "0b100"); OR] in
        let ea = mk_enc_consts p (`User []) in
        let st = mk_state ea "" in
        let c = enc_program ea st in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: Z3.Expr.t] ~printer:Z3.Expr.to_string
          (senum 5) (eval_stack st m (List.length p) 0)
      );

    (* xor *)

    "0 ^ 1 is 1" >::(fun _ ->
        let p = [PUSH (Val "0"); PUSH (Val "1"); XOR] in
        let ea = mk_enc_consts p (`User []) in
        let st = mk_state ea "" in
        let c = enc_program ea st in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: Z3.Expr.t] ~printer:Z3.Expr.to_string
          (senum 1) (eval_stack st m (List.length p) 0)
      );

    "1 ^ 1 is 0" >::(fun _ ->
        let p = [PUSH (Val "1"); PUSH (Val "1"); XOR] in
        let ea = mk_enc_consts p (`User []) in
        let st = mk_state ea "" in
        let c = enc_program ea st in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: Z3.Expr.t] ~printer:Z3.Expr.to_string
          (senum 0) (eval_stack st m (List.length p) 0)
      );

    "0 ^ 0 is 0" >::(fun _ ->
        let p = [PUSH (Val "0"); PUSH (Val "0"); XOR] in
        let ea = mk_enc_consts p (`User []) in
        let st = mk_state ea "" in
        let c = enc_program ea st in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: Z3.Expr.t] ~printer:Z3.Expr.to_string
          (senum 0) (eval_stack st m (List.length p) 0)
      );

    "1 ^ 0 is 1" >::(fun _ ->
        let p = [PUSH (Val "1"); PUSH (Val "0"); XOR] in
        let ea = mk_enc_consts p (`User []) in
        let st = mk_state ea "" in
        let c = enc_program ea st in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: Z3.Expr.t] ~printer:Z3.Expr.to_string
          (senum 1) (eval_stack st m (List.length p) 0)
      );

    "XOR is cancellative (0b101)" >::(fun _ ->
        let p = [PUSH (Val "0b101"); PUSH (Val "0b101"); XOR] in
        let ea = mk_enc_consts p (`User []) in
        let st = mk_state ea "" in
        let c = enc_program ea st in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: Z3.Expr.t] ~printer:Z3.Expr.to_string
          (senum 0) (eval_stack st m (List.length p) 0)
      );

    "0b101 ^ 0b100 is 0b001" >::(fun _ ->
        let p = [PUSH (Val "0b101"); PUSH (Val "0b100"); XOR] in
        let ea = mk_enc_consts p (`User []) in
        let st = mk_state ea "" in
        let c = enc_program ea st in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: Z3.Expr.t] ~printer:Z3.Expr.to_string
          (senum 1) (eval_stack st m (List.length p) 0)
      );

    (* eq *)

    "0 = 0 is 1" >::(fun _ ->
        let p = [PUSH (Val "0"); PUSH (Val "0"); EQ] in
        let ea = mk_enc_consts p (`User []) in
        let st = mk_state ea "" in
        let c = enc_program ea st in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: Z3.Expr.t] ~printer:Z3.Expr.to_string
          (senum 1) (eval_stack st m (List.length p) 0)
      );

    "1 = 0 is 0" >::(fun _ ->
        let p = [PUSH (Val "0"); PUSH (Val "1"); EQ] in
        let ea = mk_enc_consts p (`User []) in
        let st = mk_state ea "" in
        let c = enc_program ea st in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: Z3.Expr.t] ~printer:Z3.Expr.to_string
          (senum 0) (eval_stack st m (List.length p) 0)
      );

    "0 = 1 is 0" >::(fun _ ->
        let p = [PUSH (Val "1"); PUSH (Val "0"); EQ] in
        let ea = mk_enc_consts p (`User []) in
        let st = mk_state ea "" in
        let c = enc_program ea st in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: Z3.Expr.t] ~printer:Z3.Expr.to_string
          (senum 0) (eval_stack st m (List.length p) 0)
      );

    "1 = 1 is 1" >::(fun _ ->
        let p = [PUSH (Val "1"); PUSH (Val "1"); EQ] in
        let ea = mk_enc_consts p (`User []) in
        let st = mk_state ea "" in
        let c = enc_program ea st in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: Z3.Expr.t] ~printer:Z3.Expr.to_string
          (senum 1) (eval_stack st m (List.length p) 0)
      );

    "-1 = 1 is 0" >::(fun _ ->
        let p = [PUSH (Val "1"); PUSH (Val "-1"); EQ] in
        let ea = mk_enc_consts p (`User []) in
        let st = mk_state ea "" in
        let c = enc_program ea st in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: Z3.Expr.t] ~printer:Z3.Expr.to_string
          (senum 0) (eval_stack st m (List.length p) 0)
      );

    (* lt *)

    "0 < 0 is 0" >::(fun _ ->
        let p = [PUSH (Val "0"); PUSH (Val "0"); LT] in
        let ea = mk_enc_consts p (`User []) in
        let st = mk_state ea "" in
        let c = enc_program ea st in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: Z3.Expr.t] ~printer:Z3.Expr.to_string
          (senum 0) (eval_stack st m (List.length p) 0)
      );

    "1 < 0 is 0" >::(fun _ ->
        let p = [PUSH (Val "0"); PUSH (Val "1"); LT] in
        let ea = mk_enc_consts p (`User []) in
        let st = mk_state ea "" in
        let c = enc_program ea st in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: Z3.Expr.t] ~printer:Z3.Expr.to_string
          (senum 0) (eval_stack st m (List.length p) 0)
      );

    "0 < 1 is 1" >::(fun _ ->
        let p = [PUSH (Val "1"); PUSH (Val "0"); LT] in
        let ea = mk_enc_consts p (`User []) in
        let st = mk_state ea "" in
        let c = enc_program ea st in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: Z3.Expr.t] ~printer:Z3.Expr.to_string
          (senum 1) (eval_stack st m (List.length p) 0)
      );

    "1 < -1 is 1 (unsigned LT)" >::(fun _ ->
        let p = [PUSH (Val "-1"); PUSH (Val "1"); LT] in
        let ea = mk_enc_consts p (`User []) in
        let st = mk_state ea "" in
        let c = enc_program ea st in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: Z3.Expr.t] ~printer:Z3.Expr.to_string
          (senum 1) (eval_stack st m (List.length p) 0)
      );

    "-1 < 1 is 0 (unsigned LT)" >::(fun _ ->
        let p = [PUSH (Val "1"); PUSH (Val "-1"); LT] in
        let ea = mk_enc_consts p (`User []) in
        let st = mk_state ea "" in
        let c = enc_program ea st in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: Z3.Expr.t] ~printer:Z3.Expr.to_string
          (senum 0) (eval_stack st m (List.length p) 0)
      );

    (* gt *)

    "0 > 0 is 0" >::(fun _ ->
        let p = [PUSH (Val "0"); PUSH (Val "0"); GT] in
        let ea = mk_enc_consts p (`User []) in
        let st = mk_state ea "" in
        let c = enc_program ea st in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: Z3.Expr.t] ~printer:Z3.Expr.to_string
          (senum 0) (eval_stack st m (List.length p) 0)
      );

    "1 > 0 is 1" >::(fun _ ->
        let p = [PUSH (Val "0"); PUSH (Val "1"); GT] in
        let ea = mk_enc_consts p (`User []) in
        let st = mk_state ea "" in
        let c = enc_program ea st in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: Z3.Expr.t] ~printer:Z3.Expr.to_string
          (senum 1) (eval_stack st m (List.length p) 0)
      );

    "0 > 1 is 0" >::(fun _ ->
        let p = [PUSH (Val "1"); PUSH (Val "0"); GT] in
        let ea = mk_enc_consts p (`User []) in
        let st = mk_state ea "" in
        let c = enc_program ea st in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: Z3.Expr.t] ~printer:Z3.Expr.to_string
          (senum 0) (eval_stack st m (List.length p) 0)
      );

    "1 > -1 is 0 (unsigned GT)" >::(fun _ ->
        let p = [PUSH (Val "-1"); PUSH (Val "1"); GT] in
        let ea = mk_enc_consts p (`User []) in
        let st = mk_state ea "" in
        let c = enc_program ea st in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: Z3.Expr.t] ~printer:Z3.Expr.to_string
          (senum 0) (eval_stack st m (List.length p) 0)
      );

    "-1 > 1 is 1 (unsigned GT)" >::(fun _ ->
        let p = [PUSH (Val "1"); PUSH (Val "-1"); GT] in
        let ea = mk_enc_consts p (`User []) in
        let st = mk_state ea "" in
        let c = enc_program ea st in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: Z3.Expr.t] ~printer:Z3.Expr.to_string
          (senum 1) (eval_stack st m (List.length p) 0)
      );

    (* slt *)

    "0 <_signed 0 is 0" >::(fun _ ->
        let p = [PUSH (Val "0"); PUSH (Val "0"); SLT] in
        let ea = mk_enc_consts p (`User []) in
        let st = mk_state ea "" in
        let c = enc_program ea st in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: Z3.Expr.t] ~printer:Z3.Expr.to_string
          (senum 0) (eval_stack st m (List.length p) 0)
      );

    "1 <_signed 0 is 0" >::(fun _ ->
        let p = [PUSH (Val "0"); PUSH (Val "1"); SLT] in
        let ea = mk_enc_consts p (`User []) in
        let st = mk_state ea "" in
        let c = enc_program ea st in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: Z3.Expr.t] ~printer:Z3.Expr.to_string
          (senum 0) (eval_stack st m (List.length p) 0)
      );

    "0 <_signed 1 is 1" >::(fun _ ->
        let p = [PUSH (Val "1"); PUSH (Val "0"); SLT] in
        let ea = mk_enc_consts p (`User []) in
        let st = mk_state ea "" in
        let c = enc_program ea st in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: Z3.Expr.t] ~printer:Z3.Expr.to_string
          (senum 1) (eval_stack st m (List.length p) 0)
      );

    "1 <_signed -1 is 0" >::(fun _ ->
        let p = [PUSH (Val "-1"); PUSH (Val "1"); SLT] in
        let ea = mk_enc_consts p (`User []) in
        let st = mk_state ea "" in
        let c = enc_program ea st in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: Z3.Expr.t] ~printer:Z3.Expr.to_string
          (senum 0) (eval_stack st m (List.length p) 0)
      );

    "-1 <_signed 1 is 1" >::(fun _ ->
        let p = [PUSH (Val "1"); PUSH (Val "-1"); SLT] in
        let ea = mk_enc_consts p (`User []) in
        let st = mk_state ea "" in
        let c = enc_program ea st in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: Z3.Expr.t] ~printer:Z3.Expr.to_string
          (senum 1) (eval_stack st m (List.length p) 0)
      );

    (* sgt *)

    "0 >_signed 0 is 0" >::(fun _ ->
        let p = [PUSH (Val "0"); PUSH (Val "0"); SGT] in
        let ea = mk_enc_consts p (`User []) in
        let st = mk_state ea "" in
        let c = enc_program ea st in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: Z3.Expr.t] ~printer:Z3.Expr.to_string
          (senum 0) (eval_stack st m (List.length p) 0)
      );

    "1 >_signed 0 is 1" >::(fun _ ->
        let p = [PUSH (Val "0"); PUSH (Val "1"); SGT] in
        let ea = mk_enc_consts p (`User []) in
        let st = mk_state ea "" in
        let c = enc_program ea st in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: Z3.Expr.t] ~printer:Z3.Expr.to_string
          (senum 1) (eval_stack st m (List.length p) 0)
      );

    "0 >_signed 1 is 0" >::(fun _ ->
        let p = [PUSH (Val "1"); PUSH (Val "0"); SGT] in
        let ea = mk_enc_consts p (`User []) in
        let st = mk_state ea "" in
        let c = enc_program ea st in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: Z3.Expr.t] ~printer:Z3.Expr.to_string
          (senum 0) (eval_stack st m (List.length p) 0)
      );

    "1 >_signed -1 is 1" >::(fun _ ->
        let p = [PUSH (Val "-1"); PUSH (Val "1"); SGT] in
        let ea = mk_enc_consts p (`User []) in
        let st = mk_state ea "" in
        let c = enc_program ea st in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: Z3.Expr.t] ~printer:Z3.Expr.to_string
          (senum 1) (eval_stack st m (List.length p) 0)
      );

    "-1 >_signed 1 is 0" >::(fun _ ->
        let p = [PUSH (Val "1"); PUSH (Val "-1"); SGT] in
        let ea = mk_enc_consts p (`User []) in
        let st = mk_state ea "" in
        let c = enc_program ea st in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: Z3.Expr.t] ~printer:Z3.Expr.to_string
          (senum 0) (eval_stack st m (List.length p) 0)
      );

    (* not *)

    "not 0b001 is 0b110" >::(fun _ ->
        let p = [PUSH (Val "1"); NOT] in
        let ea = mk_enc_consts p (`User []) in
        let st = mk_state ea "" in
        let c = enc_program ea st in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: Z3.Expr.t] ~printer:Z3.Expr.to_string
          (senum 6) (eval_stack st m (List.length p) 0)
      );

    "not 0b000 is 0b111" >::(fun _ ->
        let p = [PUSH (Val "0"); NOT] in
        let ea = mk_enc_consts p (`User []) in
        let st = mk_state ea "" in
        let c = enc_program ea st in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: Z3.Expr.t] ~printer:Z3.Expr.to_string
          (senum 7) (eval_stack st m (List.length p) 0)
      );

    "not 0b101 is 0b010" >::(fun _ ->
        let p = [PUSH (Val "0b101"); NOT] in
        let ea = mk_enc_consts p (`User []) in
        let st = mk_state ea "" in
        let c = enc_program ea st in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: Z3.Expr.t] ~printer:Z3.Expr.to_string
          (senum 2) (eval_stack st m (List.length p) 0)
      );

    (* push *)

    "top of the stack is the pushed element after a PUSH">:: (fun _ ->
        let p = [PUSH (Val "5")] in
        let ea = mk_enc_consts p (`User []) in
        let st = mk_state ea "" in
        let c = enc_program ea st in
        let m = solve_model_exn [c] in
        assert_equal
          ~cmp:[%eq: Z3.Expr.t]
          ~printer:Z3.Expr.to_string
          (senum 5)
          (eval_stack st m (List.length p) 0)
      );

    (* SWAP *)

    "swap I two elements on stack" >::(fun _ ->
        let p = [PUSH (Val "1"); PUSH (Val "2"); SWAP I] in
        let ea = mk_enc_consts p `All in
        let st = mk_state ea "" in
        let c = enc_program ea st in
        let m = solve_model_exn [c] in
        assert_equal
          ~cmp:[%eq: Z3.Expr.t list]
          ~printer:(List.to_string ~f:Z3.Expr.to_string)
          [senum 2; senum 1]
          [(eval_stack st m (List.length p) 0); (eval_stack st m (List.length p) 1)]
      );

    "swap I with only one element" >::(fun _ ->
        let p = [PUSH (Val "1"); SWAP I] in
        let ea = mk_enc_consts p `All in
        let st = mk_state ea "" in
        (* allow to instantiate variables when evaluating model *)
        let c = foralls ea.xs (enc_program ea st) in
        let m = solve_model_exn [c] in
        assert_equal
          ~cmp:[%eq: Z3.Expr.t list]
          ~printer:(List.to_string ~f:Z3.Expr.to_string)
          [senum 1; senum 2]
          [(eval_stack ~xs:[senum 2] st m (List.length p) 0);
           (eval_stack ~xs:[senum 2] st m (List.length p) 1)]
      );

    "swap I with no elements" >::(fun _ ->
        let p = [SWAP I] in
        let ea = mk_enc_consts p `All in
        let st = mk_state ea "" in
        (* allow to instantiate variables when evaluating model *)
        let c = foralls ea.xs (enc_program ea st) in
        let m = solve_model_exn [c] in
        assert_equal
          ~cmp:[%eq: Z3.Expr.t list]
          ~printer:(List.to_string ~f:Z3.Expr.to_string)
          [senum 1; senum 2]
          [(eval_stack ~xs:[senum 2; senum 1] st m (List.length p) 0);
           (eval_stack ~xs:[senum 2; senum 1] st m (List.length p) 1)]
      );

     "elements after swap II" >::(fun _ ->
        let p = [PUSH (Val "1"); PUSH (Val "2"); PUSH (Val "3"); SWAP II] in
        let ea = mk_enc_consts p (`User []) in
        let st = mk_state ea "" in
        let c = enc_program ea st in
        let m = solve_model_exn [c] in
        assert_equal
          ~cmp:[%eq: Z3.Expr.t list]
          ~printer:(List.to_string ~f:Z3.Expr.to_string)
          [senum 3; senum 2; senum 1]
          [eval_stack st m (List.length p) 0;
           eval_stack st m (List.length p) 1;
           eval_stack st m (List.length p) 2;]
      );

     "preserve elements between swap III" >::(fun _ ->
        let p = [PUSH (Val "1"); PUSH (Val "2"); PUSH (Val "3"); PUSH (Val "4"); SWAP III] in
        let ea = mk_enc_consts p (`User []) in
        let st = mk_state ea "" in
        let c = enc_program ea st in
        let m = solve_model_exn [c] in
        assert_equal
          ~cmp:[%eq: Z3.Expr.t list]
          ~printer:(List.to_string ~f:Z3.Expr.to_string)
          [senum 2; senum 3]
          [eval_stack st m (List.length p) 1;
           eval_stack st m (List.length p) 2;]
      );

    (* dup *)

    "duplicate top element" >:: (fun _ ->
        let p = [PUSH (Val "1"); DUP I] in
        let ea = mk_enc_consts p (`User []) in
        let st = mk_state ea "" in
        let c = enc_program ea st in
        let m = solve_model_exn [c] in
        assert_equal
          ~cmp:[%eq: Z3.Expr.t list]
          ~printer:(List.to_string ~f:Z3.Expr.to_string)
          [senum 1; senum 1]
          [eval_stack st m (List.length p) 0;
           eval_stack st m (List.length p) 1;]
      );

    "DUP I with no elements" >::(fun _ ->
        let p = [DUP I] in
        let ea = mk_enc_consts p `All in
        let st = mk_state ea "" in
        (* allow to instantiate variables when evaluating model *)
        let c = foralls ea.xs (enc_program ea st) in
        let m = solve_model_exn [c] in
        assert_equal
          ~cmp:[%eq: Z3.Expr.t list]
          ~printer:(List.to_string ~f:Z3.Expr.to_string)
          [senum 1; senum 1]
          [(eval_stack ~xs:[senum 1] st m (List.length p) 0);
           (eval_stack ~xs:[senum 1] st m (List.length p) 1)]
      );
  ] @
  (List.map all_of_idx ~f:(fun idx ->
       "effect of DUP " ^ show_idx idx >:: (fun _ ->
           let i = idx_to_enum idx in
           let ip = List.init i ~f:(fun n -> PUSH (Val (Int.to_string n))) in
           let p = ip @ [DUP idx] in
           let ea = mk_enc_consts p (`User []) in
           let st = mk_state ea "" in
           let c = enc_program ea st in
           let m = solve_model_exn [c] in
           assert_equal ~cmp:[%eq: Z3.Expr.t] ~printer:Z3.Expr.to_string
             (eval_stack st m (List.length p) i)
             (eval_stack st m (List.length p) 0)
         ))) @
  (List.map all_of_idx ~f:(fun idx ->
       "preservation of elements between DUP " ^ show_idx idx >:: (fun _ ->
           let i = idx_to_enum idx in
           let ip = List.init i ~f:(fun n -> PUSH (Val (Int.to_string n))) in
           let p = ip @ [DUP idx] in
           let ea = mk_enc_consts p (`User []) in
           let st = mk_state ea "" in
           let c = enc_program ea st in
           let m = solve_model_exn [c] in
           assert_equal
             ~cmp:[%eq: Z3.Expr.t list]
             ~printer:(List.to_string ~f:Z3.Expr.to_string)
             (List.init (i - 1) ~f:(fun k -> (eval_stack st m (List.length p) (k + 1))))
             (List.init (i - 1) ~f:(fun k -> (eval_stack st m (List.length ip) (k + 1))))
         )))

let pres_stack =
  (* test preservation of stack elements for all opcodes *)
  List.map Instruction.encodable
    ~f:(fun oc -> "preservation of stack elements by " ^ [%show: Instruction.t] oc
                  >:: (fun _ -> test_stack_pres oc))

let stack_ctr =
  (* test all instructions manipulate stack counter correctly *)
  List.map Instruction.encodable
    ~f:(fun oc -> "stack_ctr is changed correctly by " ^ [%show: Instruction.t] oc
                  >:: (fun _ -> test_stack_ctr [oc])) @
  [
    "test a program leading to an empty stack">:: (fun _ ->
        test_stack_ctr [PUSH (Val "1"); PUSH (Val "1"); ADD; POP]
      );

    "test stack counter for empty program">:: (fun _ ->
        test_stack_ctr []
      );
  ]

let exc_halt =
  (* test all instructions preserve exceptional halting *)
  List.map Instruction.encodable
    ~f:(fun oc -> "exc_halt is preserved by " ^ [%show: Instruction.t] oc
                  >:: (fun _ -> test_exc_halt_pres [oc])) @
  (* test no exceptional halting due to stack underflow *)
  List.map Instruction.encodable
    ~f:(fun oc -> "no exc_halt due to stack underflow by "  ^ [%show: Instruction.t] oc
                  >:: (fun _ -> test_no_exc_halt [oc])) @
  [
    "valid program does not halt exceptionally">:: (fun _ ->
        test_no_exc_halt [ADD; SUB]
      );

    "PUSHing too many elements leads to a stack overflow">:: (fun _ ->
        let max = Int.pow 2 sas in
        let p = List.init max ~f:(fun _ -> PUSH (Val "1")) in
        let ea = mk_enc_consts p (`User []) in
        let st = mk_state ea "" in
        let c = enc_program ea st in
        let m = solve_model_exn [c] in
        assert_equal
          ~cmp:[%eq: Z3.Expr.t]
          ~printer:Z3.Expr.to_string
          top
          (eval_exc_halt st m (List.length p))
      );

    "exceptional halt persists for multiple instructions">:: (fun _ ->
        test_exc_halt_pres [SUB; PUSH (Val "3")]
      );
  ]

let forced_stack_underflow =
  (* test below use hack to erase xs to start from emtpy stack *)
  [
    "add with only one element">:: (fun _ ->
        let p = [PUSH (Val "3"); ADD] in
        let ea = mk_enc_consts p (`User []) in
        let st = mk_state {ea with p = []} "" in
        let c =
          init {ea with p = []} st <&>
          enc_instruction ea st (num 0) (List.nth_exn p 0) <&>
          enc_instruction ea st (num 1) (List.nth_exn p 1)
        in
        let m = solve_model_exn [c] in
        assert_equal
          ~cmp:[%eq: Z3.Expr.t]
          ~printer:Z3.Expr.to_string
          top
          (eval_exc_halt st m (List.length p))
      );

    "add with empty stack">:: (fun _ ->
        let p = [ADD] in
        let ea = mk_enc_consts p (`User []) in
        let st = mk_state {ea with p = []} "" in
        let c = init {ea with p = []} st <&>
                enc_instruction ea st (num 0) ADD in
        let m = solve_model_exn [c] in
        assert_equal
          ~cmp:[%eq: Z3.Expr.t]
          ~printer:Z3.Expr.to_string
          top
          (eval_exc_halt st m (List.length p))
      );

    "SUB with only one element">:: (fun _ ->
        let p = [PUSH (Val "3"); SUB] in
        let ea = mk_enc_consts p (`User []) in
        let st = mk_state {ea with p = []} "" in
        let c =
          init {ea with p = []} st <&>
          enc_instruction ea st (num 0) (List.nth_exn p 0) <&>
          enc_instruction ea st (num 1) (List.nth_exn p 1)
        in
        let m = solve_model_exn [c] in
        assert_equal
          ~cmp:[%eq: Z3.Expr.t]
          ~printer:Z3.Expr.to_string
          top
          (eval_exc_halt st m (List.length p))
      );

    "sub with empty stack">:: (fun _ ->
        let p = [SUB] in
        let ea = mk_enc_consts p (`User []) in
        let st = mk_state {ea with p = []} "" in
        let c =
          init {ea with p = []} st <&>
          enc_instruction ea st (num 0) (List.nth_exn p 0)
        in
        let m = solve_model_exn [c] in
        assert_equal
          ~cmp:[%eq: Z3.Expr.t]
          ~printer:Z3.Expr.to_string
          top
          (eval_exc_halt st m (List.length p))
      );

    "pop on empty stack leads to stack underflow" >:: (fun _ ->
        let p = [POP] in
        let ea = mk_enc_consts p (`User []) in
        let st = mk_state {ea with p = []} "" in
        let c =
          init {ea with p = []} st <&>
          enc_instruction ea st (num 0) (List.nth_exn p 0)
        in
        let m = solve_model_exn [c] in
        assert_equal
          ~cmp:[%eq: Z3.Expr.t]
          ~printer:Z3.Expr.to_string
          top
          (eval_exc_halt st m (List.length p))
      );
  ]

let gas_cost =
  [
    "after 0 instruction no gas has been used">::(fun _ ->
        let ea = mk_enc_consts [] (`User []) in
        let st = mk_state ea "" in
        let c = init ea st in
        let m = solve_model_exn [c] in
        assert_equal
          ~cmp:[%eq: Z3.Expr.t]
          ~printer:Z3.Expr.to_string
          (num 0)
          (eval_gas st m 0)
      );

    "after some instruction some gas has been used">::(fun _ ->
        let p = [PUSH (Val "6"); PUSH (Val "2"); ADD] in
        let ea = mk_enc_consts p (`User []) in
        let st = mk_state ea "" in
        let c = enc_program ea st in
        let m = solve_model_exn [c] in
        assert_equal
          ~cmp:[%eq: Z3.Expr.t]
          ~printer:Z3.Expr.to_string
          (num @@ total_gas_cost p)
          (eval_gas st m (List.length p))
      );
  ]

let misc =
  [
    (* enc dec opcode *)

    "encoding and decoding an opcode is the identity">:: (fun _ ->
        let ea = mk_enc_consts [] (`User [SUB; ADD; POP]) in
        assert_equal ~cmp:[%eq: Instruction.t] ~printer:[%show: Instruction.t]
          ADD (dec_opcode ea (enc_opcode ea ADD))
      );

    (* init *)

    "model of the initial stack holds 0 for every stack address">:: (fun _ ->
        let ea = mk_enc_consts [] (`User []) in
        let st = mk_state ea "" in
        let c = init ea st in
        let m = solve_model_exn [c] in
        let sk_size = (Int.pow 2 sas) - 1 in
        assert_equal
          ~cmp:[%eq: Z3.Expr.t list]
          ~printer:(List.to_string ~f:Z3.Expr.to_string)
          (List.init sk_size ~f:(fun _ -> senum 0))
          (List.init sk_size ~f:(eval_stack st m 0))
      );

    (* stack_depth *)

    "No negative stack depth, sufficient arguments" >::(fun _ ->
        let p = [PUSH (Val "1"); PUSH (Val "1"); PUSH (Val "1"); SUB] in
        assert_equal ~cmp:[%eq: int] ~printer:[%show: int]
          0 (stack_depth p)
      );

    "Stack depth of SUB" >::(fun _ ->
        let p = [SUB] in
        assert_equal ~cmp:[%eq: int] ~printer:[%show: int]
          2 (stack_depth p)
      );

    "Stack depth of exactly enough arguments" >::(fun _ ->
        let p = [PUSH (Val "1"); PUSH (Val "1"); SUB] in
        assert_equal ~cmp:[%eq: int] ~printer:[%show: int]
          0 (stack_depth p)
      );

    "Stack depth when starting with SUB, go positive, but then go deeper" >::(fun _ ->
        let p = [SUB; PUSH (Val "1"); PUSH (Val "1"); ADD; ADD; ADD] in
        assert_equal ~cmp:[%eq: int] ~printer:[%show: int]
          3 (stack_depth p)
      );

    (* sis_of_progr / Instruction.all *)

    "compute instruction set of given program" >::(fun _ ->
        let p = [SUB; PUSH (Val "1"); PUSH (Val "1"); ADD; ADD; PUSH (Val "2"); POP] in
        assert_equal ~cmp:[%eq: Program.t] ~printer:[%show: Program.t]
          [SUB; PUSH Tmpl; ADD; POP] (sis_of_progr p)
      );

    "list of all instructions" >::(fun _ ->
        assert_bool "not all instructions present"
          (List.for_all [ADD; MUL; PUSH Tmpl; POP; SUB]
             ~f:(fun i -> List.mem Instruction.all i ~equal:[%eq: Instruction.t]))
      );

    (* splitting programs into basic blocks *)

    "program with nothing to split" >:: (fun _ ->
        assert_equal ~cmp:[%eq: Program.bb list] ~printer:[%show: Program.bb list]
          [Next [ADD; SUB; POP]]
          (split_into_bbs [ADD; SUB; POP])
      );

    "split at JUMPDEST" >:: (fun _ ->
        assert_equal ~cmp:[%eq: Program.bb list] ~printer:[%show: Program.bb list]
          [Next [ADD]; Next [JUMPDEST; SUB]]
          (split_into_bbs [ADD; JUMPDEST; SUB])
      );

    "split at JUMP" >:: (fun _ ->
        assert_equal ~cmp:[%eq: Program.bb list] ~printer:[%show: Program.bb list]
          [Terminal ([ADD], JUMP); Next [SUB]]
          (split_into_bbs [ADD; JUMP; SUB])
      );

    "split program at multiple locations" >::(fun _ ->
        let p =
          [OR; ADD; SWAP I; JUMPDEST; MLOAD; POP; JUMP; DUP III;
           PUSH (Val "0"); ISZERO; JUMPI; POP; RETURN]
        in
        assert_equal ~cmp:[%eq: Program.bb list] ~printer:[%show: Program.bb list]
          [Next [OR; ADD; SWAP I]; Terminal ([JUMPDEST; MLOAD; POP], JUMP);
           Terminal ([DUP III; PUSH (Val "0"); ISZERO], JUMPI);
           Terminal ([POP], RETURN)]
          (split_into_bbs p)
      );
]

let suite =
  sesort := bv_sort ses;
  sasort := bv_sort sas;
  "suite" >:::
  effect @ pres_stack @ stack_ctr @ exc_halt @ forced_stack_underflow
  @ gas_cost @ misc

let () =
  run_test_tt_main suite
