open OUnit2
open Evmenc
open Z3util
open Core

let solve_model_exn cs =
  let slvr = Z3.Solver.mk_simple_solver !ctxt in
  let () = Z3.Solver.add slvr cs in
  match Z3.Solver.check slvr [] with
  | Z3.Solver.SATISFIABLE ->
    begin
      match Z3.Solver.get_model slvr with
      | Some m -> m
      | None -> failwith "SAT but no model"
    end
  | Z3.Solver.UNSATISFIABLE -> failwith "UNSAT"
  | Z3.Solver.UNKNOWN -> failwith (Z3.Solver.get_reason_unknown slvr)

let eval_stack_exn st m i n =
  match Z3.Model.eval m (st.stack <@@> [num i; bvnum n sas]) true with
  | Some e -> e
  | None -> failwith "could not eval stack"

let suite =
  "suite" >:::
  [
    (* init *)

    "formula for stack is initialized with 0">:: (fun _ ->
        let st = mk_state in
        assert_equal
          ~cmp:[%eq: string]
          ~printer:[%show: string]
          "(and (forall ((n (_ BitVec 4))) (= (stack 0 n) #x00)) (= (sc 0) #x0))"
          (Z3.Expr.to_string (init st))
      );

    "model of the initial stack holds 0 for every stack address">:: (fun _ ->
        let st = mk_state in
        let c = init st in
        let m = solve_model_exn [c] in
        let sk_size = (Int.pow 2 sas) - 1 in
        assert_equal
          ~cmp:[%eq: Z3.Expr.t list]
          ~printer:(List.to_string ~f:Z3.Expr.to_string)
          (List.init sk_size ~f:(fun _ -> bvnum 0 ses))
          (List.init sk_size ~f:(eval_stack_exn st m 0))
      );

    (* add *)

    "formula for add">:: (fun _ ->
        let st = mk_state in
        let one = bvnum 1 ses in
        let st' =
          let open Z3Ops in
          (st.stack @@ [num 0; bvnum 0 sas] == one) &&
          (st.stack @@ [num 0; bvnum 1 sas] == one)
        in
        assert_equal
          ~cmp:[%eq: string]
          ~printer:[%show: string]
          ""
          (Z3.Expr.to_string st')
      );

  ]

let () =
  run_test_tt_main suite
