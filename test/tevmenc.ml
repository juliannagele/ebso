open OUnit2
open Evmenc

let suite =
  "suite" >:::
  [
    "formula for stack is initialized with 0">:: (fun _ ->
        let st = mk_state in
        assert_equal
          ~cmp:[%eq: string]
          ~printer:[%show: string]
          (Z3.Expr.to_string (init st))
          "(forall ((n (_ BitVec 4))) (= (stack 0 n) #x00))"
      );

  ]

let () =
  run_test_tt_main suite
