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

let suite =
  (* set low for fast testing *)
  Word.set_wsz 3; SI.set_sas 10;
  "suite" >:::
  [
    "correct candidate program" >::(fun _ ->
        let p = [ADD;] in
        let pc = [ADD;] in
        let cis = `User [] in
        let ea = Enc_consts.mk p cis in
        let js = List.init (List.length pc) ~f:(fun i -> intconst ("j" ^ Int.to_string i)) in
        let c = enc_classic_so_test ea pc js in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: Program.t] ~printer:[%show: Program.t]
          [ADD;] (dec_classic_super_opt ea m pc js)
      );

    "correct candidate program with one PUSH" >::(fun _ ->
        let p = [PUSH (Word (Val "1"));] in
        let pc = [PUSH Tmpl] in
        let cis = `User [] in
        let ea = Enc_consts.mk p cis in
        let js = List.init (List.length pc) ~f:(fun i -> intconst ("j" ^ Int.to_string i)) in
        let c = enc_classic_so_test ea pc js in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: Program.t] ~printer:[%show: Program.t]
          [PUSH (Word (Val "1"))] (dec_classic_super_opt ea m pc js)
      );

    "incorrect candidate program with one PUSH" >::(fun _ ->
        let p = [PUSH (Word (Val "1"));] in
        let pc = [ADD] in
        let cis = `User [] in
        let ea = Enc_consts.mk p cis in
        let js = List.init (List.length pc) ~f:(fun i -> intconst ("j" ^ Int.to_string i)) in
        let c = enc_classic_so_test ea pc js in
        assert_bool "not unsat" (is_unsat [c])
      );

    "correct candidate program with two PUSHs" >::(fun _ ->
        let p = [PUSH (Word (Val "2")); PUSH (Word (Val "1"))] in
        let pc = [PUSH Tmpl; PUSH Tmpl] in
        let cis = `User [] in
        let ea = Enc_consts.mk p cis in
        let js = List.init (List.length pc) ~f:(fun i -> intconst ("j" ^ Int.to_string i)) in
        let c = enc_classic_so_test ea pc js in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: Program.t] ~printer:[%show: Program.t]
          [PUSH (Word (Val "2")); PUSH (Word (Val "1"))] (dec_classic_super_opt ea m pc js)
      );

    "incorrect candidate program with two PUSHs" >::(fun _ ->
        let p = [PUSH (Word (Val "2")); PUSH (Word (Val "1"))] in
        let pc = [PUSH Tmpl] in
        let cis = `User [] in
        let ea = Enc_consts.mk p cis in
        let js = List.init (List.length pc) ~f:(fun i -> intconst ("j" ^ Int.to_string i)) in
        let c = enc_classic_so_test ea pc js in
        assert_bool "not unsat" (is_unsat [c])
      );

    "correct candidate program with two PUSHs and optimization" >::(fun _ ->
        let p = [PUSH (Word (Val "2")); PUSH (Word (Val "1")); ADD] in
        let pc = [PUSH Tmpl;] in
        let cis = `User [] in
        let ea = Enc_consts.mk p cis in
        let js = List.init (List.length pc) ~f:(fun i -> intconst ("j" ^ Int.to_string i)) in
        let c = enc_classic_so_test ea pc js in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: Program.t] ~printer:[%show: Program.t]
          [PUSH (Word (Val "3"))] (dec_classic_super_opt ea m pc js)
      );

    "correct candidate program with three PUSHs and optimization" >::(fun _ ->
        let p = [PUSH (Word (Val "2")); PUSH (Word (Val "1")); PUSH (Word (Val "1")); ADD] in
        let pc = [PUSH Tmpl; DUP I] in
        let cis = `User [] in
        let ea = Enc_consts.mk p cis in
        let js = List.init (List.length pc) ~f:(fun i -> intconst ("j" ^ Int.to_string i)) in
        let c = enc_classic_so_test ea pc js in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: Program.t] ~printer:[%show: Program.t]
          [PUSH (Word (Val "2")); DUP I] (dec_classic_super_opt ea m pc js)
      );

    "correct candidate program which requires reordering" >::(fun _ ->
        let p = [PUSH (Word (Val "2")); PUSH (Word (Val "1")); PUSH (Word (Val "1")); ADD] in
        let pc = [DUP I; PUSH Tmpl] in
        let cis = `User [] in
        let ea = Enc_consts.mk p cis in
        let js = List.init (List.length pc) ~f:(fun i -> intconst ("j" ^ Int.to_string i)) in
        let c = enc_classic_so_test ea pc js in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: Program.t] ~printer:[%show: Program.t]
          [PUSH (Word (Val "2")); DUP I] (dec_classic_super_opt ea m pc js)
      );

  ]

let () =
  run_test_tt_main suite
