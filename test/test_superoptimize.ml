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

let suite =
  (* set low for fast testing *)
  set_wsz 3; set_sas 6;
  "suite" >:::
  [
    (* enc_search_space *)

    "search for 1 instruction program">::(fun _ ->
        let p = [PUSH (Val "1")] in
        let cis = `User [PUSH (Val "1")] in
        let ea = mk_enc_consts p cis in
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
          (enc_opcode ea (PUSH (Val "1")))
          (eval_fis ea m 0)
      );

    "search for 3 instruction program">::(fun _ ->
        let p = [PUSH (Val "1"); PUSH (Val "1"); ADD] in
        let cis = `User [PUSH (Val "1"); ADD] in
        let ea = mk_enc_consts p cis in
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
          [enc_opcode ea (PUSH (Val "1"))
          ; enc_opcode ea (PUSH (Val "1"))
          ; enc_opcode ea ADD
          ]
          [eval_fis ea m 0; eval_fis ea m 1; eval_fis ea m 2]
      );

    "cis contains unused instructions ">::(fun _ ->
        let p = [PUSH (Val "1")] in
        let cis = `User [PUSH (Val "1"); PUSH (Val "2"); ADD; SUB] in
        let ea = mk_enc_consts p cis in
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
          (enc_opcode ea (PUSH (Val "1")))
          (eval_fis ea m 0)
      );

    "cis does not contain required instruction">::(fun _ ->
        let p = [PUSH (Val "1")] in
        let cis = `User [ADD; SUB] in
        let ea = mk_enc_consts p cis in
        let st = mk_state ea "" in
        let c =
          enc_program ea st <&>
          enc_search_space ea st <&>
          (ea.kt <==> (num (List.length p)))
        in
        assert_bool "not unsat" (is_unsat [c])
      );

    (* enc_equivalence *)

    "search for 1 instruction program with equivalence constraint">::(fun _ ->
        let p = [PUSH (Val "1")] in
        let cis = `User [PUSH (Val "1")] in
        let ea = mk_enc_consts p cis in
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
          (enc_opcode ea (PUSH (Val "1")))
          (eval_fis ea m 0)
      );

    "search for 3 instruction program with equivalence constraint">::(fun _ ->
        let p = [PUSH (Val "1"); PUSH (Val "1"); ADD] in
        let cis = `User [PUSH (Val "1"); ADD] in
        let ea = mk_enc_consts p cis in
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
          [enc_opcode ea (PUSH (Val "1"))
          ; enc_opcode ea (PUSH (Val "1"))
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
        let sk_size = (Int.pow 2 !sas) - 1 in
        assert_equal
          ~cmp:[%eq: Z3.Expr.t list]
          ~printer:(List.to_string ~f:Z3.Expr.to_string)
          (List.init sk_size ~f:(fun _ -> senum 0))
          (List.init sk_size ~f:(eval_stack stt m 0))
      );

    (* template argument for PUSH *)

    "search for 1 instruction program with template (fis)">::(fun _ ->
        let p = [PUSH (Val "1")] in
        let cis = `User [PUSH Tmpl] in
        let ea = mk_enc_consts p cis in
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
        let p = [PUSH (Val "1")] in
        let cis = `User [PUSH Tmpl] in
        let ea = mk_enc_consts p cis in
        let st = mk_state ea "" in
        let c =
          enc_program ea st <&>
          enc_search_space ea st <&>
          (ea.kt <==> (num (List.length p)))
        in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: string] ~printer:[%show: string]
          "1" (eval_a ea m 0)
      );

    "search for 3 instruction program with template (fis)">::(fun _ ->
        let p = [PUSH (Val "1"); PUSH (Val "1"); ADD] in
        let cis = `User [PUSH Tmpl; ADD] in
        let ea = mk_enc_consts p cis in
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
        let p = [PUSH (Val "1"); PUSH (Val "1"); ADD] in
        let cis = `User [PUSH Tmpl; ADD] in
        let ea = mk_enc_consts p cis in
        let st = mk_state ea "" in
        let c =
          enc_program ea st <&>
          enc_search_space ea st <&>
          (ea.kt <==> (num (List.length p)))
        in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: string list] ~printer:[%show: string list]
          ["1"; "1"] [eval_a ea m 0; eval_a ea m 1]
      );

    (* super optimize *)

    "super optimize PUSH PUSH ADD to PUSH" >::(fun _ ->
        let p = [PUSH (Val "1"); PUSH (Val "1"); ADD] in
        let cis = `User [PUSH (Val "2"); PUSH (Val "1"); ADD; SUB] in
        let ea = mk_enc_consts p cis in
        let c = enc_super_opt ea in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: Program.t] ~printer:[%show: Program.t]
          [PUSH (Val "2")] (dec_super_opt ea m)
      );

    "super optimize PUSH and POP" >::(fun _ ->
        let p = [PUSH (Val "1"); POP;] in
        let cis = `User [PUSH Tmpl; POP;] in
        let ea = mk_enc_consts p cis in
        let c = enc_super_opt ea in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: Program.t] ~printer:[%show: Program.t]
          [] (dec_super_opt ea m)
      );

    "super optimize x * 0 to POP; PUSH 0" >::(fun _ ->
        let p = [PUSH (Val "0"); MUL] in
        let cis = `User [PUSH Tmpl; POP; MUL; ADD] in
        let ea = mk_enc_consts p cis in
        let c = enc_super_opt ea in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: Program.t] ~printer:[%show: Program.t]
          [POP; PUSH (Val "0")] (dec_super_opt ea m)
      );

    "super optimize x * 1 to x" >::(fun _ ->
        let p = [PUSH (Val "1"); MUL] in
        let cis = `User [PUSH Tmpl; POP; MUL; ADD] in
        let ea = mk_enc_consts p cis in
        let c = enc_super_opt ea in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: Program.t] ~printer:[%show: Program.t]
          [] (dec_super_opt ea m)
      );

    "super optimize PUSH PUSH ADD to PUSH with template" >::(fun _ ->
        let p = [PUSH (Val "1"); PUSH (Val "1"); ADD] in
        let cis = `User [PUSH Tmpl; ADD; SUB] in
        let ea = mk_enc_consts p cis in
        let c = enc_super_opt ea in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: Program.t] ~printer:[%show: Program.t]
          [PUSH (Val "2")] (dec_super_opt ea m)
      );

    (* enc_super_opt with initial words *)

    "super optimize x + 0 with one initial word on stack" >::(fun _ ->
        let p = [PUSH (Val "0"); ADD] in
        let cis = `User [PUSH Tmpl; ADD] in
        let ea = mk_enc_consts p cis in
        let c = enc_super_opt ea in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: Program.t] ~printer:[%show: Program.t]
          [] (dec_super_opt ea m)
      );

    "super optimize with two initial words on stack" >: test_case ~length:Long (fun _ ->
        let p = [ADD; PUSH (Val "0"); ADD] in
        let cis = `User [ADD] in
        let ea = mk_enc_consts p cis in
        let c = enc_super_opt ea in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: Program.t] ~printer:[%show: Program.t]
          [ADD] (dec_super_opt ea m)
      );

    "super optimize 3 + (0 - x) to (3 - x) " >::(fun _ ->
        let p = [PUSH (Val "0"); SUB; PUSH (Val "3"); ADD;] in
        let cis = `User [PUSH Tmpl; ADD; SUB;] in
        let ea = mk_enc_consts p cis in
        let c = enc_super_opt ea in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: Program.t] ~printer:[%show: Program.t]
          [PUSH (Val "3"); SUB] (dec_super_opt ea m)
      );

    (* superoptimize constant uninterpreted instructions *)

    "super optimize NUMBER POP" >:: (fun _ ->
        let p = [NUMBER; POP] in
        let cis = `Progr in
        let ea = mk_enc_consts p cis in
        let c = enc_super_opt ea in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: Program.t] ~printer:[%show: Program.t]
          [] (dec_super_opt ea m)
      );

    "super optimize NUMBER PUSH 0 ADD" >:: (fun _ ->
        let p = [NUMBER; PUSH (Val "0"); ADD] in
        let cis = `Progr in
        let ea = mk_enc_consts p cis in
        let c = enc_super_opt ea in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: Program.t] ~printer:[%show: Program.t]
          [NUMBER] (dec_super_opt ea m)
      );

    "super optimize NUMBER NUMBER NUMBER POP" >:: (fun _ ->
        let p = [NUMBER; NUMBER; NUMBER; POP] in
        let cis = `Progr in
        let ea = mk_enc_consts p cis in
        let c = enc_super_opt ea in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: Program.t] ~printer:[%show: Program.t]
          [NUMBER; NUMBER] (dec_super_opt ea m)
      );

    "super optimize NUMBER DUP1" >:: (fun _ ->
        let p = [NUMBER; DUP I] in
        let cis = `Progr in
        let ea = mk_enc_consts p cis in
        let c = enc_super_opt ea in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: Program.t] ~printer:[%show: Program.t]
          [NUMBER; NUMBER] (dec_super_opt ea m)
      );

    (* superoptimize uninterpreted instructions with argument *)

    "basic, already optimal test" >: test_case ~length:Long (fun _ ->
        let p = [PUSH (Val "1"); BALANCE] in
        let cis = `Progr in
        let ea = mk_enc_consts p cis in
        let c = enc_super_opt ea in
        assert_bool "not unsat" (is_unsat [c])
      );

    "twice BALANCE for same address optimizes to DUP" >: test_case ~length:Long (fun _ ->
        let p = [PUSH (Val "1"); BALANCE; PUSH (Val "1"); BALANCE] in
        let cis = `User [PUSH Tmpl; BALANCE; DUP I] in
        let ea = mk_enc_consts p cis in
        let c = enc_super_opt ea in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: Program.t] ~printer:[%show: Program.t]
          [PUSH (Val "1"); BALANCE; DUP I]  (dec_super_opt ea m)
      );

    "twice BALANCE for different address does not optimize" >:: (fun _ ->
        let p = [PUSH (Val "1"); BALANCE; PUSH (Val "2"); BALANCE] in
        let cis = `Progr in
        let ea = mk_enc_consts p cis in
        let c = enc_super_opt ea in
        assert_bool "not unsat" (is_unsat [c])
      );

    "twice BALANCE for same address to be computed optimizes to DUP" >:: (fun _ ->
        let p = [PUSH (Val "2"); BALANCE; PUSH (Val "1"); PUSH (Val "1"); ADD; BALANCE] in
        let cis = `User [PUSH Tmpl; BALANCE; DUP I] in
        let ea = mk_enc_consts p cis in
        let c = enc_super_opt ea in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: Program.t] ~printer:[%show: Program.t]
          [PUSH (Val "2"); BALANCE; DUP I]  (dec_super_opt ea m)
      );

   "POPing BALANCE optimizes to POP to pop argument of BALANCE" >:: (fun _ ->
        let p = [BALANCE; POP] in
        let cis = `Progr in
        let ea = mk_enc_consts p cis in
        let c = enc_super_opt ea in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: Program.t] ~printer:[%show: Program.t]
          [POP] (dec_super_opt ea m)
      );

    "twice BALANCE for same address given as initial stack arg">: test_case ~length:Long (fun _ ->
        let p = [DUP I; BALANCE; SWAP I; BALANCE] in
        let cis = `Progr in
        let ea = mk_enc_consts p cis in
        let c = enc_super_opt ea in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: Program.t] ~printer:[%show: Program.t]
          [BALANCE; DUP I] (dec_super_opt ea m)
      );

  ]

let () =
  run_test_tt_main suite
