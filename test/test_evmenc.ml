open OUnit2
open Evmenc
open Z3util
open Core

let suite =
  "suite" >:::
  [
    (* enc dec opcode *)

    "encoding and decoding an opcode is the identity">:: (fun _ ->
        let ea = mk_enc_consts [] [SUB; ADD; POP] in
        assert_equal ~cmp:[%eq: instr] ~printer:[%show: instr]
          ADD (dec_opcode ea (enc_opcode ea ADD))
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
        let p = [PUSH (Val 4); PUSH (Val 5); ADD] in
        let ea = mk_enc_consts p [] in
        let c = enc_program ea st in
        let m = solve_model_exn [c] in
        assert_equal
          ~cmp:[%eq: Z3.Expr.t]
          ~printer:Z3.Expr.to_string
          (bvnum 9 ses)
          (eval_stack st m (List.length p) 0)
      );

    "check that adding does not change element below">:: (fun _ ->
        let st = mk_state "" in
        let p = [PUSH (Val 3); PUSH (Val 4); PUSH (Val 5); ADD] in
        let ea = mk_enc_consts p [] in
        let c = enc_program ea st in
        let m = solve_model_exn [c] in
        assert_equal
          ~cmp:[%eq: Z3.Expr.t]
          ~printer:Z3.Expr.to_string
          (bvnum 3 ses)
          (eval_stack st m (List.length p) 0)
      );

    "add with only one element">:: (fun _ ->
        let st = mk_state "" in
        let p = [PUSH (Val 3); ADD] in
        let ea = mk_enc_consts p [] in
        let c = enc_program ea st in
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
        let ea = mk_enc_consts p [] in
        let c = enc_program ea st in
        let m = solve_model_exn [c] in
        assert_equal
          ~cmp:[%eq: Z3.Expr.t]
          ~printer:Z3.Expr.to_string
          top
          (eval_exc_halt st m (List.length p))
      );

    "add two elements does not lead to stack underflow">:: (fun _ ->
        let st = mk_state "" in
        let p = [PUSH (Val 4); PUSH (Val 5); ADD] in
        let ea = mk_enc_consts p [] in
        let c = enc_program ea st in
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
        let p = [PUSH (Val 8); PUSH (Val 3); SUB] in
        let ea = mk_enc_consts p [] in
        let c = enc_program ea st in
        let m = solve_model_exn [c] in
        assert_equal
          ~cmp:[%eq: Z3.Expr.t]
          ~printer:Z3.Expr.to_string
          (bvnum 5 ses)
          (eval_stack st m (List.length p) 0)
      );

    "subtract two elements on the stack with negative result">:: (fun _ ->
        let st = mk_state "" in
        let p = [PUSH (Val 8); PUSH (Val 13); SUB] in
        let ea = mk_enc_consts p [] in
        let c = enc_program ea st in
        let m = solve_model_exn [c] in
        assert_equal
          ~cmp:[%eq: Z3.Expr.t]
          ~printer:Z3.Expr.to_string
          (bvnum (-5) ses)
          (eval_stack st m (List.length p) 0)
      );

    "check that subtraction does not change element below">:: (fun _ ->
        let st = mk_state "" in
        let p = [PUSH (Val 3); PUSH (Val 4); PUSH (Val 5); SUB] in
        let ea = mk_enc_consts p [] in
        let c = enc_program ea st in
        let m = solve_model_exn [c] in
        assert_equal
          ~cmp:[%eq: Z3.Expr.t]
          ~printer:Z3.Expr.to_string
          (bvnum 3 ses)
          (eval_stack st m (List.length p) 0)
      );

    "SUB with only one element">:: (fun _ ->
        let st = mk_state "" in
        let p = [PUSH (Val 3); SUB] in
        let ea = mk_enc_consts p [] in
        let c = enc_program ea st in
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
        let ea = mk_enc_consts p [] in
        let c = enc_program ea st in
        let m = solve_model_exn [c] in
        assert_equal
          ~cmp:[%eq: Z3.Expr.t]
          ~printer:Z3.Expr.to_string
          top
          (eval_exc_halt st m (List.length p))
      );

    "exceptional halt persists">:: (fun _ ->
        let st = mk_state "" in
        let p = [SUB; PUSH (Val 3)] in
        let ea = mk_enc_consts p [] in
        let c = enc_program ea st in
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
        let p = [PUSH (Val 6); PUSH (Val 2); PUSH (Val 2); ADD; SUB] in
        let ea = mk_enc_consts p [] in
        let c = enc_program ea st in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: Z3.Expr.t] ~printer:Z3.Expr.to_string
          (bvnum 2 ses) (eval_stack st m (List.length p) 0)
      );

    "valid program does not halt exceptionally">:: (fun _ ->
        let st = mk_state "" in
        let p = [PUSH (Val 6); PUSH (Val 2); PUSH (Val 2); ADD; SUB] in
        let ea = mk_enc_consts p [] in
        let c = enc_program ea st in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: Z3.Expr.t] ~printer:Z3.Expr.to_string
          btm
          (eval_exc_halt st m (List.length p))
      );

    "invalid program should halt exceptionally">:: (fun _ ->
        let st = mk_state "" in
        let p = [(PUSH (Val 2)); SUB; (PUSH (Val 2)); ADD;] in
        let ea = mk_enc_consts p [] in
        let c = enc_program ea st in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: Z3.Expr.t] ~printer:Z3.Expr.to_string
          top
          (eval_exc_halt st m (List.length p))
      );

    (* push *)

    "top of the stack is the pushed element after a PUSH">:: (fun _ ->
        let st = mk_state "" in
        let p = [PUSH (Val 5)] in
        let ea = mk_enc_consts p [] in
        let c = enc_program ea st in
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
        let ea = mk_enc_consts [] [] in
        let c =
          init st <&>
          (st.stack_ctr <@@> [num max] <==> (bvnum max sas)) <&>
          (enc_push ea (Val 5) st (num max))
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
        let p = [PUSH (Val 5)] in
        let ea = mk_enc_consts p [] in
        let c = enc_program ea st in
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
        let p = [PUSH (Val 6); PUSH (Val 2); ADD] in
        let ea = mk_enc_consts p [] in
        let c = enc_program ea st in
        let m = solve_model_exn [c] in
        assert_equal
          ~cmp:[%eq: Z3.Expr.t]
          ~printer:Z3.Expr.to_string
          (num @@ total_gas_cost p)
          (eval_gas st m (List.length p))
      );

    (* enc_search_space *)

    "search for 1 instruction program">::(fun _ ->
        let st = mk_state "" in
        let p = [PUSH (Val 1)] in
        let sis = [PUSH (Val 1)] in
        let ea = mk_enc_consts p sis in
        let c =
          enc_program ea st <&>
          enc_search_space st ea <&>
          (ea.kt <==> (num (List.length p)))
        in
        let m = solve_model_exn [c] in
        assert_equal
          ~cmp:[%eq: int]
          ~printer:[%show: int]
          (enc_opcode ea (PUSH (Val 1)))
          (eval_fis ea m 0)
      );

    "search for 3 instruction program">::(fun _ ->
        let st = mk_state "" in
        let p = [PUSH (Val 1); PUSH (Val 1); ADD] in
        let sis = [PUSH (Val 1); ADD] in
        let ea = mk_enc_consts p sis in
        let c =
          enc_program ea st <&>
          enc_search_space st ea <&>
          (ea.kt <==> (num (List.length p)))
        in
        let m = solve_model_exn [c] in
        assert_equal
          ~cmp:[%eq: int list]
          ~printer:[%show: int list]
          [enc_opcode ea (PUSH (Val 1))
          ; enc_opcode ea (PUSH (Val 1))
          ; enc_opcode ea ADD
          ]
          [eval_fis ea m 0; eval_fis ea m 1; eval_fis ea m 2]
      );

    "sis contains unused instructions ">::(fun _ ->
        let st = mk_state "" in
        let p = [PUSH (Val 1)] in
        let sis = [PUSH (Val 1); PUSH (Val 2); ADD; SUB] in
        let ea = mk_enc_consts p sis in
        let c =
          enc_program ea st <&>
          enc_search_space st ea <&>
          (ea.kt <==> (num (List.length p)))
        in
        let m = solve_model_exn [c] in
        assert_equal
          ~cmp:[%eq: int]
          ~printer:[%show: int]
          (enc_opcode ea (PUSH (Val 1)))
          (eval_fis ea m 0)
      );

    "sis does not contain required instruction">::(fun _ ->
        let st = mk_state "" in
        let p = [PUSH (Val 1)] in
        let sis = [ADD; SUB] in
        let ea = mk_enc_consts p sis in
        let c =
          enc_program ea st <&>
          enc_search_space st ea <&>
          (ea.kt <==> (num (List.length p)))
        in
        let slvr = Z3.Solver.mk_simple_solver !ctxt in
        let () = Z3.Solver.add slvr [c] in
        assert_equal
          Z3.Solver.UNSATISFIABLE
          (Z3.Solver.check slvr [])
      );

    (* enc_equivalence *)

    "search for 1 instruction program with equivalence constraint">::(fun _ ->
        let st = mk_state "" in
        let p = [PUSH (Val 1)] in
        let sis = [PUSH (Val 1)] in
        let ea = mk_enc_consts p sis in
        let c =
          enc_program ea st <&>
          enc_search_space st ea <&>
          enc_equivalence st st (List.length p) ea.kt
        in
        let m = solve_model_exn [c] in
        assert_equal
          ~cmp:[%eq: int]
          ~printer:[%show: int]
          (enc_opcode ea (PUSH (Val 1)))
          (eval_fis ea m 0)
      );

    "search for 3 instruction program with equivalence constraint">::(fun _ ->
        let st = mk_state "" in
        let p = [PUSH (Val 1); PUSH (Val 1); ADD] in
        let sis = [PUSH (Val 1); ADD] in
        let ea = mk_enc_consts p sis in
        let c =
          enc_program ea st <&>
          enc_search_space st ea <&>
          enc_equivalence st st (List.length p) ea.kt
        in
        let m = solve_model_exn [c] in
        assert_equal
          ~cmp:[%eq: int list]
          ~printer:[%show: int list]
          [enc_opcode ea (PUSH (Val 1))
          ; enc_opcode ea (PUSH (Val 1))
          ; enc_opcode ea ADD
          ]
          [eval_fis ea m 0; eval_fis ea m 1; eval_fis ea m 2]
      );

    "equivalence constraint forces inital stack for target program">:: (fun _ ->
        let sts = mk_state "_s" in
        let stt = mk_state "_t" in
        let kt = intconst "k" in
        let c = init sts <&> enc_equivalence sts stt 0 kt in
        let m = solve_model_exn [c] in
        let sk_size = (Int.pow 2 sas) - 1 in
        assert_equal
          ~cmp:[%eq: Z3.Expr.t list]
          ~printer:(List.to_string ~f:Z3.Expr.to_string)
          (List.init sk_size ~f:(fun _ -> bvnum 0 ses))
          (List.init sk_size ~f:(eval_stack stt m 0))
      );

    (* super optimize *)

    "super optimize PUSH PUSH ADD to PUSH" >::(fun _ ->
        let open Z3Ops in
        let p = [PUSH (Val 1); PUSH (Val 1); ADD] in
        let sts = mk_state "_s" in
        let stt = mk_state "_t" in
        let ks = List.length p in
        let sis = [PUSH (Val 2); PUSH (Val 1); ADD; SUB] in
        let ea = mk_enc_consts p sis in
        let c =
          enc_program ea sts &&
          enc_search_space stt ea &&
          enc_equivalence sts stt ks ea.kt &&
          sts.used_gas @@ [num ks] > stt.used_gas @@ [ea.kt]
        in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: instr list] ~printer:[%show: instr list]
          [PUSH (Val 2)] (dec_super_opt m ea)
      );

    (* template argument for PUSH *)

    "search for 1 instruction program with template (fis)">::(fun _ ->
        let st = mk_state "" in
        let p = [PUSH (Val 1)] in
        let sis = [PUSH Tmpl] in
        let ea = mk_enc_consts p sis in
        let c =
          enc_program ea st <&>
          enc_search_space st ea <&>
          (ea.kt <==> (num (List.length p)))
        in
        let m = solve_model_exn [c] in
        assert_equal
          ~cmp:[%eq: int]
          ~printer:[%show: int]
          (enc_opcode ea (PUSH Tmpl))
          (eval_fis ea m 0)
      );

    "search for 1 instruction program with template (a)">::(fun _ ->
        let st = mk_state "" in
        let p = [PUSH (Val 1)] in
        let sis = [PUSH Tmpl] in
        let ea = mk_enc_consts p sis in
        let c =
          enc_program ea st <&>
          enc_search_space st ea <&>
          (ea.kt <==> (num (List.length p)))
        in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: int] ~printer:[%show: int]
          1 (eval_a ea m 0)
      );

    "search for 3 instruction program with template (fis)">::(fun _ ->
        let st = mk_state "" in
        let p = [PUSH (Val 1); PUSH (Val 1); ADD] in
        let sis = [PUSH Tmpl; ADD] in
        let ea = mk_enc_consts p sis in
        let c =
          enc_program ea st <&>
          enc_search_space st ea <&>
          (ea.kt <==> (num (List.length p)))
        in
        let m = solve_model_exn [c] in
        assert_equal
          ~cmp:[%eq: int list]
          ~printer:[%show: int list]
          [ enc_opcode ea (PUSH Tmpl)
          ; enc_opcode ea (PUSH Tmpl)
          ; enc_opcode ea ADD
          ]
          [eval_fis ea m 0; eval_fis ea m 1; eval_fis ea m 2]
      );

    "search for 3 instruction program with template (a)">::(fun _ ->
        let st = mk_state "" in
        let p = [PUSH (Val 1); PUSH (Val 1); ADD] in
        let sis = [PUSH Tmpl; ADD] in
        let ea = mk_enc_consts p sis in
        let c =
          enc_program ea st <&>
          enc_search_space st ea <&>
          (ea.kt <==> (num (List.length p)))
        in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: int list] ~printer:[%show: int list]
          [1; 1] [eval_a ea m 0; eval_a ea m 1]
      );

    "super optimize PUSH PUSH ADD to PUSH with template" >::(fun _ ->
        let open Z3Ops in
        let p = [PUSH (Val 1); PUSH (Val 1); ADD] in
        let sts = mk_state "_s" in
        let stt = mk_state "_t" in
        let ks = List.length p in
        let sis = [PUSH Tmpl; ADD; SUB] in
        let ea = mk_enc_consts p sis in
        let c =
          enc_program ea sts &&
          enc_search_space stt ea &&
          enc_equivalence sts stt ks ea.kt &&
          sts.used_gas @@ [num ks] > stt.used_gas @@ [ea.kt]
        in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: instr list] ~printer:[%show: instr list]
          [PUSH (Val 2)] (dec_super_opt m ea)
      );

  ]

let () =
  run_test_tt_main suite
