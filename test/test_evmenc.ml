open OUnit2
open Evmenc
open Z3util
open Core

let solve_model_exn cs =
  let slvr = Z3.Solver.mk_simple_solver !ctxt in
  let () = Z3.Solver.add slvr cs in
  match Z3.Solver.check slvr [] with
  | Z3.Solver.SATISFIABLE ->
    begin
      match Z3.Solver.get_model slvr with
      | Some m -> m
      | None -> failwith "SAT but no model"
    end
  | Z3.Solver.UNSATISFIABLE -> failwith "UNSAT"
  | Z3.Solver.UNKNOWN -> failwith (Z3.Solver.get_reason_unknown slvr)

let eval_stack_exn st m i n =
  match Z3.Model.eval m (st.stack <@@> [num i; bvnum n sas]) true with
  | Some e -> e
  | None -> failwith "could not eval stack"

let eval_exc_halt st m i =
  match Z3.Model.eval m (st.exc_halt <@@> [num i]) true with
  | Some e -> e
  | None -> failwith "could not eval exc_halt"

let suite =
  "suite" >:::
  [
    (* init *)

    "formula for stack is initialized with 0">:: (fun _ ->
        let st = mk_state in
        assert_equal
          ~cmp:[%eq: string]
          ~printer:Fn.id
          "(and (forall ((n (_ BitVec 4))) (= (stack 0 n) #x00))
     (= (sc 0) #x0)
     (= (exc_halt 0) false)
     (= (used_gas 0) 0))"
          (Z3.Expr.to_string (init st))
      );

    "model of the initial stack holds 0 for every stack address">:: (fun _ ->
        let st = mk_state in
        let c = init st in
        let m = solve_model_exn [c] in
        let sk_size = (Int.pow 2 sas) - 1 in
        assert_equal
          ~cmp:[%eq: Z3.Expr.t list]
          ~printer:(List.to_string ~f:Z3.Expr.to_string)
          (List.init sk_size ~f:(fun _ -> bvnum 0 ses))
          (List.init sk_size ~f:(eval_stack_exn st m 0))
      );

    (* add *)
    "add two elements on the stack">:: (fun _ ->
        let st = mk_state in
        let c =
          init st <&>
          enc_push 4 st (num 0) <&>
          enc_push 5 st (num 1) <&>
          enc_add st (num 2)
        in
        let m = solve_model_exn [c] in
        assert_equal
          ~cmp:[%eq: Z3.Expr.t]
          ~printer:Z3.Expr.to_string
          (bvnum 9 ses)
          (eval_stack_exn st m 3 0)
      );

    "check that adding does not change element below">:: (fun _ ->
        let st = mk_state in
        let c =
          init st <&>
          enc_push 3 st (num 0) <&>
          enc_push 4 st (num 1) <&>
          enc_push 5 st (num 2) <&>
          enc_add st (num 3)
        in
        let m = solve_model_exn [c] in
        assert_equal
          ~cmp:[%eq: Z3.Expr.t]
          ~printer:Z3.Expr.to_string
          (bvnum 3 ses)
          (eval_stack_exn st m 3 0)
      );

    "add with only one element">:: (fun _ ->
        let st = mk_state in
        let c = init st <&> enc_push 3 st (num 0) <&> enc_add st (num 1) in
        let m = solve_model_exn [c] in
        assert_equal
          ~cmp:[%eq: Z3.Expr.t]
          ~printer:Z3.Expr.to_string
          top
          (eval_exc_halt st m 2)
      );

    "add with empty stack">:: (fun _ ->
        let st = mk_state in
        let c = init st <&> enc_add st (num 0) in
        let m = solve_model_exn [c] in
        assert_equal
          ~cmp:[%eq: Z3.Expr.t]
          ~printer:Z3.Expr.to_string
          top
          (eval_exc_halt st m 1)
      );

    (* sub *)
    "subtract two elements on the stack">:: (fun _ ->
        let st = mk_state in
        let c =
          init st <&>
          enc_push 8 st (num 0) <&>
          enc_push 3 st (num 1) <&>
          enc_sub st (num 2)
        in
        let m = solve_model_exn [c] in
        assert_equal
          ~cmp:[%eq: Z3.Expr.t]
          ~printer:Z3.Expr.to_string
          (bvnum 5 ses)
          (eval_stack_exn st m 3 0)
      );

    "subtract two elements on the stack with negative result">:: (fun _ ->
        let st = mk_state in
        let c =
          init st <&>
          enc_push 8 st (num 0) <&>
          enc_push 13 st (num 1) <&>
          enc_sub st (num 2)
        in
        let m = solve_model_exn [c] in
        assert_equal
          ~cmp:[%eq: Z3.Expr.t]
          ~printer:Z3.Expr.to_string
          (bvnum (-5) ses)
          (eval_stack_exn st m 3 0)
      );

    "check that subtraction does not change element below">:: (fun _ ->
        let st = mk_state in
        let c =
          init st <&>
          enc_push 3 st (num 0) <&>
          enc_push 4 st (num 1) <&>
          enc_push 5 st (num 2) <&>
          enc_sub st (num 3)
        in
        let m = solve_model_exn [c] in
        assert_equal
          ~cmp:[%eq: Z3.Expr.t]
          ~printer:Z3.Expr.to_string
          (bvnum 3 ses)
          (eval_stack_exn st m 3 0)
      );

    "SUB with only one element">:: (fun _ ->
        let st = mk_state in
        let c = init st <&> enc_push 3 st (num 0) <&> enc_sub st (num 1) in
        let m = solve_model_exn [c] in
        assert_equal
          ~cmp:[%eq: Z3.Expr.t]
          ~printer:Z3.Expr.to_string
          top
          (eval_exc_halt st m 2)
      );

    "sub with empty stack">:: (fun _ ->
        let st = mk_state in
        let c = init st <&> enc_sub st (num 0) in
        let m = solve_model_exn [c] in
        assert_equal
          ~cmp:[%eq: Z3.Expr.t]
          ~printer:Z3.Expr.to_string
          top
          (eval_exc_halt st m 1)
      );

    (* add and sub *)
    "combine add and sub">:: (fun _ ->
        let st = mk_state in
        let c =
          init st <&>
          enc_push 6 st (num 0) <&>
          enc_push 2 st (num 1) <&>
          enc_push 2 st (num 2) <&>
          enc_add st (num 3) <&>
          enc_sub st (num 4)
        in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: Z3.Expr.t] ~printer:Z3.Expr.to_string
          (bvnum 2 ses) (eval_stack_exn st m 5 0)
      );

    (* push *)
    "top of the stack is the pushed element after a PUSH">:: (fun _ ->
        let st = mk_state in
        let c = init st <&> enc_push 5 st (num 0) in
        let m = solve_model_exn [c] in
        assert_equal
          ~cmp:[%eq: Z3.Expr.t]
          ~printer:Z3.Expr.to_string
          (bvnum 5 ses)
          (eval_stack_exn st m 1 0)
      );

    "PUSHing too many elements leads to a stack overflow">:: (fun _ ->
        let st = mk_state in
        let max = Int.pow 2 sas - 1 in
        let c =
          init st <&>
          (st.stack_ctr <@@> [num max] <==> (bvnum max sas)) <&>
          (enc_push 5 st (num max))
        in
        let m = solve_model_exn [c] in
        assert_equal
          ~cmp:[%eq: Z3.Expr.t]
          ~printer:Z3.Expr.to_string
          top
          (eval_exc_halt st m (max + 1))
      );

  ]

let () =
  run_test_tt_main suite
