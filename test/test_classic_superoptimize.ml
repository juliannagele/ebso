open Core
open OUnit2
open Z3util
open Instruction
open Evmenc

let suite =
  (* set low for fast testing *)
  set_wsz 256; set_sas 10;
  "suite" >:::
  [
    "correct candidate program" >::(fun _ ->
        let p = [ADD;] in
        let pc = [ADD;] in
        let cis = `User [] in
        let ea = mk_enc_consts p cis in
        let c = enc_classic_so_test ea pc in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: Program.t] ~printer:[%show: Program.t]
          [ADD;] (dec_classic_super_opt ea m pc)
      );

    "correct candidate program with one PUSH" >::(fun _ ->
        let p = [PUSH (Val "1");] in
        let pc = [PUSH Tmpl] in
        let cis = `User [] in
        let ea = mk_enc_consts p cis in
        let c = enc_classic_so_test ea pc in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: Program.t] ~printer:[%show: Program.t]
          [PUSH (Val "1")] (dec_classic_super_opt ea m pc)
      );

    "incorrect candidate program with one PUSH" >::(fun _ ->
        let p = [PUSH (Val "1");] in
        let pc = [ADD] in
        let cis = `User [] in
        let ea = mk_enc_consts p cis in
        let c = enc_classic_so_test ea pc in
        let m = solve_model [c] in
        assert_bool "not unsat" (Option.is_none m)
      );

    "correct candidate program with two PUSHs" >::(fun _ ->
        let p = [PUSH (Val "2"); PUSH (Val "1")] in
        let pc = [PUSH Tmpl; PUSH Tmpl] in
        let cis = `User [] in
        let ea = mk_enc_consts p cis in
        let c = enc_classic_so_test ea pc in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: Program.t] ~printer:[%show: Program.t]
          [PUSH (Val "2"); PUSH (Val "1")] (dec_classic_super_opt ea m pc)
      );

    "incorrect candidate program with two PUSHs" >::(fun _ ->
        let p = [PUSH (Val "2"); PUSH (Val "1")] in
        let pc = [PUSH Tmpl] in
        let cis = `User [] in
        let ea = mk_enc_consts p cis in
        let c = enc_classic_so_test ea pc in
        let m = solve_model [c] in
        assert_bool "not unsat" (Option.is_none m)
      );

    "correct candidate program with two PUSHs and optimization" >::(fun _ ->
        let p = [PUSH (Val "2"); PUSH (Val "1"); ADD] in
        let pc = [PUSH Tmpl;] in
        let cis = `User [] in
        let ea = mk_enc_consts p cis in
        let c = enc_classic_so_test ea pc in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: Program.t] ~printer:[%show: Program.t]
          [PUSH (Val "3")] (dec_classic_super_opt ea m pc)
      );

    "correct candidate program with three PUSHs and optimization" >::(fun _ ->
        let p = [PUSH (Val "2"); PUSH (Val "1"); PUSH (Val "1"); ADD] in
        let pc = [PUSH Tmpl; DUP I] in
        let cis = `User [] in
        let ea = mk_enc_consts p cis in
        let c = enc_classic_so_test ea pc in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: Program.t] ~printer:[%show: Program.t]
          [PUSH (Val "2"); DUP I] (dec_classic_super_opt ea m pc)
      );
  ]

let () =
  run_test_tt_main suite
