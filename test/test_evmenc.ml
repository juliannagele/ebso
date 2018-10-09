open OUnit2
open Evmenc
open Z3util
open Core

let suite =
  "suite" >:::
  [
    (* enc dec opcode *)

    "encoding and decoding an opcode is the identity">:: (fun _ ->
        let ea = mk_enc_consts [] (`User [SUB; ADD; POP]) in
        assert_equal ~cmp:[%eq: instr] ~printer:[%show: instr]
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
          (List.init sk_size ~f:(fun _ -> bvnum 0 ses))
          (List.init sk_size ~f:(eval_stack st m 0))
      );

    (* add *)
    "add two elements on the stack">:: (fun _ ->
        let p = [PUSH (Val 4); PUSH (Val 5); ADD] in
        let ea = mk_enc_consts p (`User []) in
        let st = mk_state ea "" in
        let c = enc_program ea st in
        let m = solve_model_exn [c] in
        assert_equal
          ~cmp:[%eq: Z3.Expr.t]
          ~printer:Z3.Expr.to_string
          (bvnum 9 ses)
          (eval_stack st m (List.length p) 0)
      );

    "check that adding does not change element below">:: (fun _ ->
        let p = [PUSH (Val 3); PUSH (Val 4); PUSH (Val 5); ADD] in
        let ea = mk_enc_consts p (`User []) in
        let st = mk_state ea "" in
        let c = enc_program ea st in
        let m = solve_model_exn [c] in
        assert_equal
          ~cmp:[%eq: Z3.Expr.t]
          ~printer:Z3.Expr.to_string
          (bvnum 3 ses)
          (eval_stack st m (List.length p) 0)
      );

    "add with only one element">:: (fun _ ->
        let p = [PUSH (Val 3); ADD] in
        let ea = mk_enc_consts p (`User []) in
        (* hack to erase xs to start from emtpy stack *)
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
        (* hack to erase xs to start from emtpy stack *)
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

    "add two elements does not lead to stack underflow">:: (fun _ ->
        let p = [PUSH (Val 4); PUSH (Val 5); ADD] in
        let ea = mk_enc_consts p (`User []) in
        let st = mk_state ea "" in
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
        let p = [PUSH (Val 3); PUSH (Val 8); SUB] in
        let ea = mk_enc_consts p (`User []) in
        let st = mk_state ea "" in
        let c = enc_program ea st in
        let m = solve_model_exn [c] in
        assert_equal
          ~cmp:[%eq: Z3.Expr.t]
          ~printer:Z3.Expr.to_string
          (bvnum 5 ses)
          (eval_stack st m (List.length p) 0)
      );

    "subtract two elements on the stack with negative result">:: (fun _ ->
        let p = [PUSH (Val 13); PUSH (Val 8); SUB] in
        let ea = mk_enc_consts p (`User []) in
        let st = mk_state ea "" in
        let c = enc_program ea st in
        let m = solve_model_exn [c] in
        assert_equal
          ~cmp:[%eq: Z3.Expr.t]
          ~printer:Z3.Expr.to_string
          (bvnum (-5) ses)
          (eval_stack st m (List.length p) 0)
      );

    "check that subtraction does not change element below">:: (fun _ ->
        let p = [PUSH (Val 3); PUSH (Val 4); PUSH (Val 5); SUB] in
        let ea = mk_enc_consts p (`User []) in
        let st = mk_state ea "" in
        let c = enc_program ea st in
        let m = solve_model_exn [c] in
        assert_equal
          ~cmp:[%eq: Z3.Expr.t]
          ~printer:Z3.Expr.to_string
          (bvnum 3 ses)
          (eval_stack st m (List.length p) 0)
      );

    "SUB with only one element">:: (fun _ ->
        let p = [PUSH (Val 3); SUB] in
        let ea = mk_enc_consts p (`User []) in
        (* hack to erase xs to start from emtpy stack *)
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
        (* hack to erase xs to start from emtpy stack *)
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

    "exceptional halt persists">:: (fun _ ->
        let p = [SUB; PUSH (Val 3)] in
        let ea = mk_enc_consts p (`User []) in
        (* hack to erase xs to start from emtpy stack *)
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

    (* add and sub *)

    "combine add and sub">:: (fun _ ->
        let p = [PUSH (Val 3); PUSH (Val 2); PUSH (Val 2); ADD; SUB] in
        let ea = mk_enc_consts p (`User []) in
        let st = mk_state ea "" in
        let c = enc_program ea st in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: Z3.Expr.t] ~printer:Z3.Expr.to_string
          (bvnum 1 ses) (eval_stack st m (List.length p) 0)
      );

    "valid program does not halt exceptionally">:: (fun _ ->
        let p = [PUSH (Val 6); PUSH (Val 2); PUSH (Val 2); ADD; SUB] in
        let ea = mk_enc_consts p (`User []) in
        let st = mk_state ea "" in
        let c = enc_program ea st in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: Z3.Expr.t] ~printer:Z3.Expr.to_string
          btm
          (eval_exc_halt st m (List.length p))
      );

    (* push *)

    "top of the stack is the pushed element after a PUSH">:: (fun _ ->
        let p = [PUSH (Val 5)] in
        let ea = mk_enc_consts p (`User []) in
        let st = mk_state ea "" in
        let c = enc_program ea st in
        let m = solve_model_exn [c] in
        assert_equal
          ~cmp:[%eq: Z3.Expr.t]
          ~printer:Z3.Expr.to_string
          (bvnum 5 ses)
          (eval_stack st m (List.length p) 0)
      );

    "PUSHing too many elements leads to a stack overflow">:: (fun _ ->
        let max = Int.pow 2 sas - 1 in
        let ea = mk_enc_consts [] (`User []) in
        let st = mk_state ea "" in
        let c =
          init ea st <&>
          (st.stack_ctr <@@> [num max] <==> (bvnum max sas)) <&>
          (enc_push ea st (num max) (Val 5))
        in
        let m = solve_model_exn [c] in
        assert_equal
          ~cmp:[%eq: Z3.Expr.t]
          ~printer:Z3.Expr.to_string
          top
          (eval_exc_halt st m (max + 1))
      );

    "PUSHing one element does not to a stack overflow">:: (fun _ ->
        let p = [PUSH (Val 5)] in
        let ea = mk_enc_consts p (`User []) in
        let st = mk_state ea "" in
        let c = enc_program ea st in
        let m = solve_model_exn [c] in
        assert_equal
          ~cmp:[%eq: Z3.Expr.t]
          ~printer:Z3.Expr.to_string
          btm
          (eval_exc_halt st m (List.length p))
      );

    (* pop *)

    "pop only touches top element">:: (fun _ ->
        let p = [PUSH (Val 2); PUSH (Val 1); POP] in
        let ea = mk_enc_consts p (`User []) in
        let st = mk_state ea "" in
        let c = enc_program ea st in
        let m = solve_model_exn [c] in
        assert_equal
          ~cmp:[%eq: Z3.Expr.t]
          ~printer:Z3.Expr.to_string
          (bvnum 2 ses)
          (eval_stack st m (List.length p) 0)
      );

    "push and pop on empty stack leads to empty stack">:: (fun _ ->
        let p = [PUSH (Val 1); POP] in
        let ea = mk_enc_consts p (`User []) in
        let st = mk_state ea "" in
        let c = enc_program ea st in
        let m = solve_model_exn [c] in
        assert_equal
          ~cmp:[%eq: Z3.Expr.t]
          ~printer:Z3.Expr.to_string
          (bvnum 0 sas)
          (eval_stack_ctr st m (List.length p))
      );

    "pop on empty stack leads to stack underflow" >:: (fun _ ->
        let p = [POP] in
        let ea = mk_enc_consts p (`User []) in
        (* hack to erase xs to start from emtpy stack *)
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

    (* gas cost *)
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
        let p = [PUSH (Val 6); PUSH (Val 2); ADD] in
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

    (* enc_search_space *)

    "search for 1 instruction program">::(fun _ ->
        let p = [PUSH (Val 1)] in
        let sis = `User [PUSH (Val 1)] in
        let ea = mk_enc_consts p sis in
        let st = mk_state ea "" in
        let c =
          enc_program ea st <&>
          enc_search_space ea st <&>
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
        let p = [PUSH (Val 1); PUSH (Val 1); ADD] in
        let sis = `User [PUSH (Val 1); ADD] in
        let ea = mk_enc_consts p sis in
        let st = mk_state ea "" in
        let c =
          enc_program ea st <&>
          enc_search_space ea st <&>
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
        let p = [PUSH (Val 1)] in
        let sis = `User [PUSH (Val 1); PUSH (Val 2); ADD; SUB] in
        let ea = mk_enc_consts p sis in
        let st = mk_state ea "" in
        let c =
          enc_program ea st <&>
          enc_search_space ea st <&>
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
        let p = [PUSH (Val 1)] in
        let sis = `User [ADD; SUB] in
        let ea = mk_enc_consts p sis in
        let st = mk_state ea "" in
        let c =
          enc_program ea st <&>
          enc_search_space ea st <&>
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
        let p = [PUSH (Val 1)] in
        let sis = `User [PUSH (Val 1)] in
        let ea = mk_enc_consts p sis in
        let st = mk_state ea "" in
        let c =
          enc_program ea st <&>
          enc_search_space ea st <&>
          enc_equivalence ea st st
        in
        let m = solve_model_exn [c] in
        assert_equal
          ~cmp:[%eq: int]
          ~printer:[%show: int]
          (enc_opcode ea (PUSH (Val 1)))
          (eval_fis ea m 0)
      );

    "search for 3 instruction program with equivalence constraint">::(fun _ ->
        let p = [PUSH (Val 1); PUSH (Val 1); ADD] in
        let sis = `User [PUSH (Val 1); ADD] in
        let ea = mk_enc_consts p sis in
        let st = mk_state ea "" in
        let c =
          enc_program ea st <&>
          enc_search_space ea st <&>
          enc_equivalence ea st st
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
        let ea = mk_enc_consts [] (`User []) in
        let sts = mk_state ea "_s" in
        let stt = mk_state ea "_t" in
        let c = init ea sts <&> enc_equivalence ea sts stt in
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
        let p = [PUSH (Val 1); PUSH (Val 1); ADD] in
        let sis = `User [PUSH (Val 2); PUSH (Val 1); ADD; SUB] in
        let ea = mk_enc_consts p sis in
        let c = enc_super_opt ea in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: progr] ~printer:[%show: progr]
          [PUSH (Val 2)] (dec_super_opt ea m)
      );

    "super optimize PUSH and POP" >::(fun _ ->
        let p = [PUSH (Val 1); POP;] in
        let sis = `User [PUSH Tmpl; POP;] in
        let ea = mk_enc_consts p sis in
        let c = enc_super_opt ea in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: progr] ~printer:[%show: progr]
          [] (dec_super_opt ea m)
      );

    "super optimize x * 0 to POP; PUSH 0" >::(fun _ ->
        let p = [PUSH (Val 0); MUL] in
        let sis = `User [PUSH Tmpl; POP; MUL; ADD] in
        let ea = mk_enc_consts p sis in
        let c = enc_super_opt ea in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: progr] ~printer:[%show: progr]
          [POP; PUSH (Val 0)] (dec_super_opt ea m)
      );

    "super optimize x * 1 to x" >::(fun _ ->
        let p = [PUSH (Val 1); MUL] in
        let sis = `User [PUSH Tmpl; POP; MUL; ADD] in
        let ea = mk_enc_consts p sis in
        let c = enc_super_opt ea in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: progr] ~printer:[%show: progr]
          [] (dec_super_opt ea m)
      );

    (* template argument for PUSH *)

    "search for 1 instruction program with template (fis)">::(fun _ ->
        let p = [PUSH (Val 1)] in
        let sis = `User [PUSH Tmpl] in
        let ea = mk_enc_consts p sis in
        let st = mk_state ea "" in
        let c =
          enc_program ea st <&>
          enc_search_space ea st <&>
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
        let p = [PUSH (Val 1)] in
        let sis = `User [PUSH Tmpl] in
        let ea = mk_enc_consts p sis in
        let st = mk_state ea "" in
        let c =
          enc_program ea st <&>
          enc_search_space ea st <&>
          (ea.kt <==> (num (List.length p)))
        in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: int] ~printer:[%show: int]
          1 (eval_a ea m 0)
      );

    "search for 3 instruction program with template (fis)">::(fun _ ->
        let p = [PUSH (Val 1); PUSH (Val 1); ADD] in
        let sis = `User [PUSH Tmpl; ADD] in
        let ea = mk_enc_consts p sis in
        let st = mk_state ea "" in
        let c =
          enc_program ea st <&>
          enc_search_space ea st <&>
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
        let p = [PUSH (Val 1); PUSH (Val 1); ADD] in
        let sis = `User [PUSH Tmpl; ADD] in
        let ea = mk_enc_consts p sis in
        let st = mk_state ea "" in
        let c =
          enc_program ea st <&>
          enc_search_space ea st <&>
          (ea.kt <==> (num (List.length p)))
        in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: int list] ~printer:[%show: int list]
          [1; 1] [eval_a ea m 0; eval_a ea m 1]
      );

    "super optimize PUSH PUSH ADD to PUSH with template" >::(fun _ ->
        let open Z3Ops in
        let p = [PUSH (Val 1); PUSH (Val 1); ADD] in
        let ks = List.length p in
        let sis = `User [PUSH Tmpl; ADD; SUB] in
        let ea = mk_enc_consts p sis in
        let sts = mk_state ea "_s" in
        let stt = mk_state ea "_t" in
        let c =
          enc_program ea sts &&
          enc_search_space ea stt &&
          enc_equivalence ea sts stt &&
          sts.used_gas @@ [num ks] > stt.used_gas @@ [ea.kt]
        in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: progr] ~printer:[%show: progr]
          [PUSH (Val 2)] (dec_super_opt ea m)
      );

    (* stack_depth *)

    "No negative stack depth, sufficient arguments" >::(fun _ ->
        let p = [PUSH (Val 1); PUSH (Val 1); PUSH (Val 1); SUB] in
        assert_equal ~cmp:[%eq: int] ~printer:[%show: int]
          0 (stack_depth p)
      );

    "Start with SUB" >::(fun _ ->
        let p = [SUB] in
        assert_equal ~cmp:[%eq: int] ~printer:[%show: int]
          2 (stack_depth p)
      );

    "Exactly enough arguments" >::(fun _ ->
        let p = [PUSH (Val 1); PUSH (Val 1); SUB] in
        assert_equal ~cmp:[%eq: int] ~printer:[%show: int]
          0 (stack_depth p)
      );

    "Start with SUB, go positive, but then go deeper" >::(fun _ ->
        let p = [SUB; PUSH (Val 1); PUSH (Val 1); ADD; ADD; ADD] in
        assert_equal ~cmp:[%eq: int] ~printer:[%show: int]
          3 (stack_depth p)
      );

    (* sis_of_progr / all_of_instr *)

    "compute instruction set of given program" >::(fun _ ->
        let p = [SUB; PUSH (Val 1); PUSH (Val 1); ADD; ADD; PUSH (Val 2); POP] in
        assert_equal ~cmp:[%eq: progr] ~printer:[%show: progr]
          [SUB; PUSH Tmpl; ADD; POP] (sis_of_progr p)
      );

    "list of all instructions" >::(fun _ ->
        assert_bool "not all instructions present"
          (List.for_all [ADD; MUL; PUSH Tmpl; POP; SUB]
             ~f:(fun i -> List.mem all_of_instr i ~equal:[%eq: instr]))
      );

    (* enc_super_opt with init stack elements *)

    "super optimize x + 0 with one init stack element" >::(fun _ ->
        let p = [PUSH (Val 0); ADD] in
        let sis = `User [PUSH Tmpl; ADD] in
        let ea = mk_enc_consts p sis in
        let c = enc_super_opt ea in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: progr] ~printer:[%show: progr]
          [] (dec_super_opt ea m)
      );

    "super optimize with two init stack elements" >: test_case ~length:Long (fun _ ->
        let p = [ADD; PUSH (Val 0); ADD] in
        let sis = `User [ADD] in
        let ea = mk_enc_consts p sis in
        let c = enc_super_opt ea in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: progr] ~printer:[%show: progr]
          [ADD] (dec_super_opt ea m)
      );

    "super optimize 3 + (0 - x) to (3 - x) " >::(fun _ ->
        let p = [PUSH (Val 0); SUB; PUSH (Val 3); ADD;] in
        let sis = `User [PUSH Tmpl; ADD; SUB;] in
        let ea = mk_enc_consts p sis in
        let c = enc_super_opt ea in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: progr] ~printer:[%show: progr]
          [PUSH (Val 3); SUB] (dec_super_opt ea m)
      );
  ]

let () =
  run_test_tt_main suite
