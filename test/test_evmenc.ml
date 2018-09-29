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

let eval_func_decl_at_i m i ?(n = []) f =
  match Z3.Model.eval m (f <@@> ([num i] @ n)) true with
  | Some e -> e
  | None -> failwith ("could not eval " ^ Z3.FuncDecl.to_string f)

let eval_stack st m i n = eval_func_decl_at_i m i ~n:[bvnum n sas] st.stack

let eval_exc_halt st m i = eval_func_decl_at_i m i st.exc_halt

let eval_gas st m i = eval_func_decl_at_i m i st.used_gas

let eval_const m k =
  match Z3.Model.eval m k true with
  | Some e -> e
  | None -> failwith ("could not eval " ^ Z3.Expr.to_string k)

let suite =
  "suite" >:::
  [
    (* enc dec opcode *)

    "encoding and decoding an opcode is the identity">:: (fun _ ->
        assert_equal ~cmp:[%eq: instr] ~printer:[%show: instr]
          ADD (dec_opcode (enc_opcode ADD))
      );

    (* init *)

    "formula for stack is initialized with 0">:: (fun _ ->
        let st = mk_state "" in
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
        let st = mk_state "" in
        let c = init st in
        let m = solve_model_exn [c] in
        let sk_size = (Int.pow 2 sas) - 1 in
        assert_equal
          ~cmp:[%eq: Z3.Expr.t list]
          ~printer:(List.to_string ~f:Z3.Expr.to_string)
          (List.init sk_size ~f:(fun _ -> bvnum 0 ses))
          (List.init sk_size ~f:(eval_stack st m 0))
      );

    (* add *)
    "add two elements on the stack">:: (fun _ ->
        let st = mk_state "" in
        let p = [PUSH 4; PUSH 5; ADD] in
        let c = enc_program st p in
        let m = solve_model_exn [c] in
        assert_equal
          ~cmp:[%eq: Z3.Expr.t]
          ~printer:Z3.Expr.to_string
          (bvnum 9 ses)
          (eval_stack st m (List.length p) 0)
      );

    "check that adding does not change element below">:: (fun _ ->
        let st = mk_state "" in
        let p = [PUSH 3; PUSH 4; PUSH 5; ADD] in
        let c = enc_program st p in
        let m = solve_model_exn [c] in
        assert_equal
          ~cmp:[%eq: Z3.Expr.t]
          ~printer:Z3.Expr.to_string
          (bvnum 3 ses)
          (eval_stack st m (List.length p) 0)
      );

    "add with only one element">:: (fun _ ->
        let st = mk_state "" in
        let p = [PUSH 3; ADD] in
        let c = enc_program st p in
        let m = solve_model_exn [c] in
        assert_equal
          ~cmp:[%eq: Z3.Expr.t]
          ~printer:Z3.Expr.to_string
          top
          (eval_exc_halt st m (List.length p))
      );

    "add with empty stack">:: (fun _ ->
        let st = mk_state "" in
        let p = [ADD] in
        let c = enc_program st p in
        let m = solve_model_exn [c] in
        assert_equal
          ~cmp:[%eq: Z3.Expr.t]
          ~printer:Z3.Expr.to_string
          top
          (eval_exc_halt st m (List.length p))
      );

    "add two elements does not lead to stack underflow">:: (fun _ ->
        let st = mk_state "" in
        let p = [PUSH 4; PUSH 5; ADD] in
        let c = enc_program st p in
        let m = solve_model_exn [c] in
        assert_equal
          ~cmp:[%eq: Z3.Expr.t]
          ~printer:Z3.Expr.to_string
          btm
          (eval_exc_halt st m (List.length p))
      );

    (* sub *)
    "subtract two elements on the stack">:: (fun _ ->
        let st = mk_state "" in
        let p = [PUSH 8; PUSH 3; SUB] in
        let c = enc_program st p in
        let m = solve_model_exn [c] in
        assert_equal
          ~cmp:[%eq: Z3.Expr.t]
          ~printer:Z3.Expr.to_string
          (bvnum 5 ses)
          (eval_stack st m (List.length p) 0)
      );

    "subtract two elements on the stack with negative result">:: (fun _ ->
        let st = mk_state "" in
        let p = [PUSH 8; PUSH 13; SUB] in
        let c = enc_program st p in
        let m = solve_model_exn [c] in
        assert_equal
          ~cmp:[%eq: Z3.Expr.t]
          ~printer:Z3.Expr.to_string
          (bvnum (-5) ses)
          (eval_stack st m (List.length p) 0)
      );

    "check that subtraction does not change element below">:: (fun _ ->
        let st = mk_state "" in
        let p = [PUSH 3; PUSH 4; PUSH 5; SUB] in
        let c = enc_program st p in
        let m = solve_model_exn [c] in
        assert_equal
          ~cmp:[%eq: Z3.Expr.t]
          ~printer:Z3.Expr.to_string
          (bvnum 3 ses)
          (eval_stack st m (List.length p) 0)
      );

    "SUB with only one element">:: (fun _ ->
        let st = mk_state "" in
        let p = [PUSH 3; SUB] in
        let c = enc_program st p in
        let m = solve_model_exn [c] in
        assert_equal
          ~cmp:[%eq: Z3.Expr.t]
          ~printer:Z3.Expr.to_string
          top
          (eval_exc_halt st m (List.length p))
      );

    "sub with empty stack">:: (fun _ ->
        let st = mk_state "" in
        let p = [SUB] in
        let c = enc_program st p in
        let m = solve_model_exn [c] in
        assert_equal
          ~cmp:[%eq: Z3.Expr.t]
          ~printer:Z3.Expr.to_string
          top
          (eval_exc_halt st m (List.length p))
      );

    "exceptional halt persists">:: (fun _ ->
        let st = mk_state "" in
        let p = [SUB; PUSH 3] in
        let c = enc_program st p in
        let m = solve_model_exn [c] in
        assert_equal
          ~cmp:[%eq: Z3.Expr.t]
          ~printer:Z3.Expr.to_string
          top
          (eval_exc_halt st m (List.length p))
      );

    (* add and sub *)
    "combine add and sub">:: (fun _ ->
        let st = mk_state "" in
        let p = [PUSH 6; PUSH 2; PUSH 2; ADD; SUB] in
        let c = enc_program st p in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: Z3.Expr.t] ~printer:Z3.Expr.to_string
          (bvnum 2 ses) (eval_stack st m (List.length p) 0)
      );

    "valid program does not halt exceptionally">:: (fun _ ->
        let st = mk_state "" in
        let p = [PUSH 6; PUSH 2; PUSH 2; ADD; SUB] in
        let c = enc_program st p in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: Z3.Expr.t] ~printer:Z3.Expr.to_string
          btm
          (eval_exc_halt st m (List.length p))
      );

    (* push *)
    "top of the stack is the pushed element after a PUSH">:: (fun _ ->
        let st = mk_state "" in
        let p = [PUSH 5] in
        let c = enc_program st p in
        let m = solve_model_exn [c] in
        assert_equal
          ~cmp:[%eq: Z3.Expr.t]
          ~printer:Z3.Expr.to_string
          (bvnum 5 ses)
          (eval_stack st m (List.length p) 0)
      );

    "PUSHing too many elements leads to a stack overflow">:: (fun _ ->
        let st = mk_state "" in
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

    "PUSHing one element does not to a stack overflow">:: (fun _ ->
        let st = mk_state "" in
        let p = [PUSH 5] in
        let c = enc_program st p in
        let m = solve_model_exn [c] in
        assert_equal
          ~cmp:[%eq: Z3.Expr.t]
          ~printer:Z3.Expr.to_string
          btm
          (eval_exc_halt st m (List.length p))
      );

    (* gas cost *)
    "after 0 instruction no gas has been used">::(fun _ ->
        let st = mk_state "" in
        let c = init st in
        let m = solve_model_exn [c] in
        assert_equal
          ~cmp:[%eq: Z3.Expr.t]
          ~printer:Z3.Expr.to_string
          (num 0)
          (eval_gas st m 0)
      );

    "after some instruction some gas has been used">::(fun _ ->
        let st = mk_state "" in
        let p = [PUSH 6; PUSH 2; ADD] in
        let c = enc_program st p in
        let m = solve_model_exn [c] in
        assert_equal
          ~cmp:[%eq: Z3.Expr.t]
          ~printer:Z3.Expr.to_string
          (num @@ total_gas_cost p)
          (eval_gas st m (List.length p))
      );

    (* enc_search_space *)
    "search for 1 instruction program (fis)">::(fun _ ->
        let st = mk_state "" in
        let p = [PUSH 1] in
        let sis = [PUSH 1] in
        let k = intconst "k" in
        let fis = func_decl "fis" [int_sort] int_sort in
        let c = enc_program st p <&> enc_search_space st k sis fis in
        let m = solve_model_exn [c] in
        assert_equal
          ~cmp:[%eq: Z3.Expr.t]
          ~printer:Z3.Expr.to_string
          (num (enc_opcode (PUSH 1)))
          (eval_func_decl_at_i m 0 fis)
      );

    "search for 1 instruction program (k)">::(fun _ ->
        let st = mk_state "" in
        let p = [PUSH 1] in
        let sis = [PUSH 1] in
        let k = intconst "k" in
        let fis = func_decl "fis" [int_sort] int_sort in
        let c = enc_program st p <&> enc_search_space st k sis fis in
        let m = solve_model_exn [c] in
        assert_equal
          ~cmp:[%eq: Z3.Expr.t]
          ~printer:Z3.Expr.to_string
          (num 1)
          (eval_const m k)
      );

  ]

let () =
  run_test_tt_main suite
