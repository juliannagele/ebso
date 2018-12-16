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
  set_wsz 2; set_sas 6;
  "suite" >:::
  [

    (* blockhash *)

    "top of the stack is some word after BLOCKHASH" >:: (fun _ ->
        let p = [BLOCKHASH] in
        let ea = mk_enc_consts p (`User []) in
        let st = mk_state ea "" in
        let c = foralls (ea.xs @ ea.uis) (enc_program ea st) in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: Z3.Expr.t] ~printer:Z3.Expr.to_string
          (senum 1)
          (eval_stack ~xs:[senum 2; senum 1; senum 2] st m (List.length p) 0)
      );

    "stack after PUSH BLOCKHASH BLOCKHASH" >: test_case ~length:Long (fun _ ->
        let p = [PUSH (Val "3"); BLOCKHASH; BLOCKHASH] in
        let ea = mk_enc_consts p (`User []) in
        let st = mk_state ea "" in
        let c = foralls ea.uis (enc_program ea st) in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: Z3.Expr.t] ~printer:Z3.Expr.to_string
          (senum 1)
          (eval_stack ~xs:[senum 2; senum 3; senum 1; senum 2] st m (List.length p) 0)
      );

    "stack after PUSH BLOCKHASH PUSH BLOCKHASH" >: test_case ~length:Long (fun _ ->
        let p = [PUSH (Val "0"); BLOCKHASH; PUSH (Val "1"); BLOCKHASH] in
        let ea = mk_enc_consts p (`User []) in
        let st = mk_state ea "" in
        let c = foralls ea.uis (enc_program ea st) in
        let m = solve_model_exn [c] in
        assert_equal
          ~cmp:[%eq: Z3.Expr.t list]
          ~printer:(List.to_string ~f:(Z3.Expr.to_string))
          [senum 3; senum 2]
          [eval_stack ~xs:[senum 3; senum 0; senum 2; senum 1] st m (List.length p) 0;
           eval_stack ~xs:[senum 3; senum 0; senum 2; senum 1] st m (List.length p) 1]
      );

    "super optimize BLOCKHASH POP" >: test_case ~length:Long  (fun _ ->
        let p = [BLOCKHASH; POP] in
        let cis = `Progr in
        let ea = mk_enc_consts p cis in
        let c = enc_super_opt ea in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: Program.t] ~printer:[%show: Program.t]
          [POP] (dec_super_opt ea m)
      );

    "super optimize BLOCKHASH PUSH 0 ADD" >: test_case ~length:Long (fun _ ->
        let p = [BLOCKHASH; PUSH (Val "0"); ADD] in
        let cis = `User [BLOCKHASH] in
        let ea = mk_enc_consts p cis in
        let c = enc_super_opt ea in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: Program.t] ~printer:[%show: Program.t]
          [BLOCKHASH] (dec_super_opt ea m)
      );

    "super optimize PUSH 0 PUSH 2 ADD BLOCKHASH" >:: (fun _ ->
        let p = [PUSH (Val "0"); PUSH (Val "1"); ADD; BLOCKHASH] in
        let cis = `Progr in
        let ea = mk_enc_consts p cis in
        let c = enc_super_opt ea in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: Program.t] ~printer:[%show: Program.t]
          [PUSH (Val "1"); BLOCKHASH] (dec_super_opt ea m)
      );

    "super optimize BLOCKHASH BLOCKHASH" >: test_case ~length:Long (fun _ ->
        let p = [BLOCKHASH; BLOCKHASH; PUSH (Val "0"); POP] in
        let cis = `Progr in
        let ea = mk_enc_consts p cis in
        let c = enc_super_opt ea in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: Program.t] ~printer:[%show: Program.t]
          [BLOCKHASH; BLOCKHASH] (dec_super_opt ea m)
      );

    "super optimize NOT BLOCKHASH" >: test_case ~length:Long (fun _ ->
        let p = [NOT; BLOCKHASH; PUSH (Val "0"); POP] in
        let cis = `Progr in
        let ea = mk_enc_consts p cis in
        let c = enc_super_opt ea in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: Program.t] ~printer:[%show: Program.t]
          [NOT; BLOCKHASH] (dec_super_opt ea m)
      );

    "super optimize PUSH 0 BLOCKHASH PUSH 0 BLOCKHASH" >: test_case ~length:Long (fun _ ->
        let p = [PUSH (Val "0"); BLOCKHASH; PUSH (Val "0"); BLOCKHASH] in
        let cis = `User [PUSH Tmpl; BLOCKHASH; DUP I] in
        let ea = mk_enc_consts p cis in
        let c = enc_super_opt ea in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: Program.t] ~printer:[%show: Program.t]
          [PUSH (Val "0"); BLOCKHASH; DUP I] (dec_super_opt ea m)
      );

    "super optimize PUSH 0 BLOCKHASH PUSH 1 BLOCKHASH" >: test_case ~length:Long (fun _ ->
        let p = [PUSH (Val "0"); BLOCKHASH; PUSH (Val "1"); BLOCKHASH] in
        let cis = `User [PUSH Tmpl; BLOCKHASH; DUP I] in
        let ea = mk_enc_consts p cis in
        let c = enc_super_opt ea in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: Program.t] ~printer:[%show: Program.t]
          [PUSH (Val "0"); BLOCKHASH; DUP I] (dec_super_opt ea m)
      );

  ]

let () =
  run_test_tt_main suite
