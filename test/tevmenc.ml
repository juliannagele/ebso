open OUnit2
open Evmenc
open Z3util
open Core

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

    "model of the initial stack holds 0 for every stack address">:: (fun _ ->
        let st = mk_state in
        let c = init st in
        let slvr = Z3.Solver.mk_simple_solver !ctxt in
        let () = Z3.Solver.add slvr [c] in
        match  Z3.Solver.check slvr [] with
        | Z3.Solver.SATISFIABLE ->
          begin
            match Z3.Solver.get_model slvr with
            | None -> failwith "SAT but no model"
            | Some m ->
              begin
                match (Z3.Model.eval m (st.stack <@@> [num 0; bvnum 0 sas]) true) with
                | Some e ->
                  assert_equal
                    ~cmp:[%eq: string]
                    ~printer:[%show: string]
                    (Z3.Expr.to_string e) "#x00"
                | None -> failwith "could not eval stack"
              end
          end
        | _ -> failwith "UNSAT/TO"
      );

  ]

let () =
  run_test_tt_main suite
