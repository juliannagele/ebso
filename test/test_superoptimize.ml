open OUnit2
open Evmenc
open Z3util
open Core

(* set low for fast testing *)
let ses = 3 and sas = 4

let suite =
  sesort := bv_sort ses;
  sasort := bv_sort sas;
  "suite" >:::
  [
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

    "super optimize PUSH PUSH ADD to PUSH with template" >::(fun _ ->
        let p = [PUSH (Val 1); PUSH (Val 1); ADD] in
        let sis = `User [PUSH Tmpl; ADD; SUB] in
        let ea = mk_enc_consts p sis in
        let c = enc_super_opt ea in
        let m = solve_model_exn [c] in
        assert_equal ~cmp:[%eq: progr] ~printer:[%show: progr]
          [PUSH (Val 2)] (dec_super_opt ea m)
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
