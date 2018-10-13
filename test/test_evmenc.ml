open OUnit2
open Evmenc
open Z3util
open Core

(* set low for fast testing *)
let ses = 3 and sas = 4

let test_stack_pres oc =
  let (d, _) = delta_alpha oc in
  (* create program that initializes stack with d + 2 values *)
  let ip = List.init (d + 2) ~f:(fun i -> PUSH (Val i)) in
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

let test_no_exc_halt p =
  let d = stack_depth p in
  (* create program that initializes stack with d values *)
  let ip = List.init d ~f:(fun i -> PUSH (Val i)) in
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
  let ip = List.init max ~f:(fun _ -> PUSH (Val 1)) in
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

let misc =
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
          (List.init sk_size ~f:(fun _ -> senum 0))
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
          (senum 9)
          (eval_stack st m (List.length p) 0)
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
          (senum 5)
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
          (senum (-5))
          (eval_stack st m (List.length p) 0)
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
          (senum 1) (eval_stack st m (List.length p) 0)
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
          (senum 5)
          (eval_stack st m (List.length p) 0)
      );

    (* pop *)

    "push and pop on empty stack leads to empty stack">:: (fun _ ->
        let p = [PUSH (Val 1); POP] in
        let ea = mk_enc_consts p (`User []) in
        let st = mk_state ea "" in
        let c = enc_program ea st in
        let m = solve_model_exn [c] in
        assert_equal
          ~cmp:[%eq: Z3.Expr.t]
          ~printer:Z3.Expr.to_string
          (sanum 0)
          (eval_stack_ctr st m (List.length p))
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
          (List.init sk_size ~f:(fun _ -> senum 0))
          (List.init sk_size ~f:(eval_stack stt m 0))
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

    (* SWAP *)

    "swap two elements on stack" >::(fun _ ->
        let p = [PUSH (Val 1); PUSH (Val 2); SWAP I] in
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

    "swap with only one element" >::(fun _ ->
        let p = [PUSH (Val 1); SWAP I] in
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

    "swap with no elements" >::(fun _ ->
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

  ]

let pres_stack =
  (* test preservation of stack elements for all opcodes *)
  List.map all_of_instr
    ~f:(fun oc -> "preservation of stack elements by " ^ [%show: instr] oc
                  >:: (fun _ -> test_stack_pres oc))

let exc_halt =
  (* test all instructions preserve exceptional halting *)
  List.map all_of_instr
    ~f:(fun oc -> "exc_halt is preserved by " ^ [%show: instr] oc
                  >:: (fun _ -> test_exc_halt_pres [oc])) @
  (* test no exceptional halting due to stack underflow *)
  List.map all_of_instr
    ~f:(fun oc -> "no exc_halt due to stack underflow by "  ^ [%show: instr] oc
                  >:: (fun _ -> test_no_exc_halt [oc])) @
  [
    "valid program does not halt exceptionally">:: (fun _ ->
        test_no_exc_halt [ADD; SUB]
      );

    "PUSHing too many elements leads to a stack overflow">:: (fun _ ->
        let max = Int.pow 2 sas in
        let p = List.init max ~f:(fun _ -> PUSH (Val 1)) in
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
  ]

let forced_stack_underflow =
  (* test below use hack to erase xs to start from emtpy stack *)
  [
    "add with only one element">:: (fun _ ->
        let p = [PUSH (Val 3); ADD] in
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
        let p = [PUSH (Val 3); SUB] in
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

let suite =
  sesort := bv_sort ses;
  sasort := bv_sort sas;
  "suite" >:::
  misc @ pres_stack @ exc_halt @ forced_stack_underflow

let () =
  run_test_tt_main suite
