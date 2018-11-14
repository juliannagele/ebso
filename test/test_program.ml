open Core
open OUnit2
open Instruction
open Program

let suite =
  "suite" >:::
  [
    (* stack_depth *)

    "No negative stack depth, sufficient arguments" >::(fun _ ->
        let p = [PUSH (Val "1"); PUSH (Val "1"); PUSH (Val "1"); SUB] in
        assert_equal ~cmp:[%eq: int] ~printer:[%show: int]
          0 (stack_depth p)
      );

    "Stack depth of SUB" >::(fun _ ->
        let p = [SUB] in
        assert_equal ~cmp:[%eq: int] ~printer:[%show: int]
          2 (stack_depth p)
      );

    "Stack depth of exactly enough arguments" >::(fun _ ->
        let p = [PUSH (Val "1"); PUSH (Val "1"); SUB] in
        assert_equal ~cmp:[%eq: int] ~printer:[%show: int]
          0 (stack_depth p)
      );

    "Stack depth when starting with SUB, go positive, but then go deeper" >::(fun _ ->
        let p = [SUB; PUSH (Val "1"); PUSH (Val "1"); ADD; ADD; ADD] in
        assert_equal ~cmp:[%eq: int] ~printer:[%show: int]
          3 (stack_depth p)
      );

    (* cis_of_progr / Instruction.all *)

    "compute instruction set of given program" >::(fun _ ->
        let p = [SUB; PUSH (Val "1"); PUSH (Val "1"); ADD; ADD; PUSH (Val "2"); POP] in
        assert_equal ~cmp:[%eq: Program.t] ~printer:[%show: Program.t]
          [SUB; PUSH Tmpl; ADD; POP] (cis_of_progr p)
      );

    "list of all instructions" >::(fun _ ->
        assert_bool "not all instructions present"
          (List.for_all [ADD; MUL; PUSH Tmpl; POP; SUB]
             ~f:(fun i -> List.mem Instruction.all i ~equal:[%eq: Instruction.t]))
      );

    (* splitting programs into basic blocks *)

    "program with nothing to split" >:: (fun _ ->
        assert_equal ~cmp:[%eq: Program.bb list] ~printer:[%show: Program.bb list]
          [Next [ADD; SUB; POP]]
          (split_into_bbs [ADD; SUB; POP])
      );

    "split at JUMPDEST" >:: (fun _ ->
        assert_equal ~cmp:[%eq: Program.bb list] ~printer:[%show: Program.bb list]
          [Next [ADD]; Next [JUMPDEST; SUB]]
          (split_into_bbs ~split_non_encodable:false [ADD; JUMPDEST; SUB])
      );

    "split at JUMP" >:: (fun _ ->
        assert_equal ~cmp:[%eq: Program.bb list] ~printer:[%show: Program.bb list]
          [Terminal ([ADD], JUMP); Next [SUB]]
          (split_into_bbs ~split_non_encodable:false [ADD; JUMP; SUB])
      );

    "split program at multiple locations" >::(fun _ ->
        let p =
          [OR; ADD; SWAP I; JUMPDEST; MLOAD; POP; JUMP; DUP III;
           PUSH (Val "0"); ISZERO; JUMPI; POP; RETURN]
        in
        assert_equal ~cmp:[%eq: Program.bb list] ~printer:[%show: Program.bb list]
          [Next [OR; ADD; SWAP I]; Terminal ([JUMPDEST; MLOAD; POP], JUMP);
           Terminal ([DUP III; PUSH (Val "0"); ISZERO], JUMPI);
           Terminal ([POP], RETURN)]
          (split_into_bbs ~split_non_encodable:false p)
      );

    "splitting a program into BBs and then concatenating them back" >::(fun _ ->
        let p =
          [OR; ADD; SWAP I; JUMPDEST; MLOAD; POP; JUMP; DUP III;
           PUSH (Val "0"); ISZERO; JUMPI; POP; RETURN]
        in
        assert_equal ~cmp:[%eq: Program.t] ~printer:[%show: Program.t]
          p
          (concat_bbs @@ split_into_bbs ~split_non_encodable:false p)
      );

    "split program at non-encodable instructions" >::(fun _ ->
        let p =
          [OR; ADD; SWAP I; JUMPDEST; MLOAD; POP; JUMP; DUP III;
           PUSH (Val "0"); ISZERO; JUMPI; POP; RETURN]
        in
        assert_equal ~cmp:[%eq: Program.bb list] ~printer:[%show: Program.bb list]
          [Next [OR; ADD; SWAP I]; NotEncodable [JUMPDEST; MLOAD];
           Terminal ([POP], JUMP);
           Terminal ([DUP III; PUSH (Val "0"); ISZERO], JUMPI);
           Terminal ([POP], RETURN)]
          (split_into_bbs p)
      );

    "splitting into BBs and concatenating back with non-encodable split" >::(fun _ ->
        let p =
          [OR; ADD; SWAP I; JUMPDEST; MLOAD; POP; JUMP; DUP III;
           PUSH (Val "0"); ISZERO; JUMPI; POP; RETURN]
        in
        assert_equal ~cmp:[%eq: Program.t] ~printer:[%show: Program.t]
          p
          (concat_bbs @@ split_into_bbs p)
      );

    (* val_to_const *)

    "replace large val with const" >:: (fun _ ->
        let v = "16" in
        let wsz = 2 in
        let p = [PUSH (Val v)] in
        assert_equal
          ~cmp:[%eq: Program.t]
          ~printer:[%show: Program.t]
          [PUSH (Const ("c" ^ v))]
          (val_to_const wsz p)
      );

    "do not replace fitting val with const" >:: (fun _ ->
        let v = "1" in
        let wsz = 2 in
        let p = [PUSH (Val v)] in
        assert_equal
          ~cmp:[%eq: Program.t]
          ~printer:[%show: Program.t]
          [PUSH (Val v)]
          (val_to_const wsz p)
      );

    "do not replace 0 with const" >:: (fun _ ->
        let v = "0" in
        let wsz = 2 in
        let p = [PUSH (Val v)] in
        assert_equal
          ~cmp:[%eq: Program.t]
          ~printer:[%show: Program.t]
          [PUSH (Val v)]
          (val_to_const wsz p)
      );

    "replace in program" >:: (fun _ ->
        let wsz = 2 in
        let p = [PUSH (Val "2"); PUSH (Val "17"); PUSH (Val "9"); ADD; PUSH (Val "100")] in
        assert_equal
          ~cmp:[%eq: Program.t]
          ~printer:[%show: Program.t]
          [PUSH (Val "2"); PUSH (Const "c17"); PUSH (Const "c9"); ADD; PUSH (Const "c100")]
          (val_to_const wsz p)
      );

    "replace same value in program" >:: (fun _ ->
        let v = "42" in
        let wsz = 2 in
        let p = [PUSH (Val v); PUSH (Val v)] in
        assert_equal
          ~cmp:[%eq: Program.t]
          ~printer:[%show: Program.t]
          [PUSH (Const ("c" ^ v)); PUSH (Const ("c" ^ v)) ]
          (val_to_const wsz p)
      );

    "replace max value and max + 1 in program" >:: (fun _ ->
        let max = "3" in
        let max_1 = "4" in
        let wsz = 2 in
        let p = [PUSH (Val max); PUSH (Val max_1)] in
        assert_equal
          ~cmp:[%eq: Program.t]
          ~printer:[%show: Program.t]
          [PUSH (Val max); PUSH (Const ("c" ^ max_1)) ]
          (val_to_const wsz p)
      );

    "replace large binary val with const" >:: (fun _ ->
        let v = "0b1001" in
        let wsz = 2 in
        let p = [PUSH (Val v)] in
        assert_equal
          ~cmp:[%eq: Program.t]
          ~printer:[%show: Program.t]
          [PUSH (Const ("c9"))]
          (val_to_const wsz p)
      );

    (* const_to_val *)

    "redeem val from const" >:: (fun _ ->
        let v = "42" in
        let p = [PUSH (Const ("c" ^ v))] in
        assert_equal
          ~cmp:[%eq: Program.t]
          ~printer:[%show: Program.t]
          [PUSH (Val v)]
          (const_to_val p)
      );

    "redeem large binary val from const" >:: (fun _ ->
        let v = "0b1001" in
        let p = [PUSH (Const ("c" ^ v))] in
        assert_equal
          ~cmp:[%eq: Program.t]
          ~printer:[%show: Program.t]
          [PUSH (Val v)]
          (const_to_val p)
      );

    "idempotent with fitting value" >:: (fun _ ->
        let v = "1" in
        let wsz = 2 in
        let p = [PUSH (Val v)] in
        assert_equal
          ~cmp:[%eq: Program.t]
          ~printer:[%show: Program.t]
          p
          (const_to_val (val_to_const wsz p))
      );

    "idempotent in large program" >:: (fun _ ->
        let wsz = 2 in
        let p = [PUSH (Val "2"); PUSH (Val "17"); PUSH (Val "9"); ADD; PUSH (Val "100")] in
        assert_equal
          ~cmp:[%eq: Program.t]
          ~printer:[%show: Program.t]
          p
          (const_to_val (val_to_const wsz p))
      );

    "idempotent with same value in program" >:: (fun _ ->
        let v = "42" in
        let wsz = 2 in
        let p = [PUSH (Val v); PUSH (Val v)] in
        assert_equal
          ~cmp:[%eq: Program.t]
          ~printer:[%show: Program.t]
          p
          (const_to_val (val_to_const wsz p))
      );

    (* consts *)

    "get constants from program" >:: (fun _ ->
        let c1 = "c123" and c2 = "c321" in
        let p = [PUSH (Val "2"); PUSH (Const c1); PUSH (Const c1); PUSH (Const c2)] in
        assert_equal
          ~cmp:[%eq: string list]
          ~printer:[%show: string list]
          [c1; c2]
          (consts p)
      );

    "values of different bases to same const" >:: (fun _ ->
        let vb = "0b1001" in
        let vd = "9" in
        let vh = "0x9" in
        let p = [PUSH (Val vb); PUSH (Val vd); PUSH (Val vh);] in
        let p' = Program.val_to_const 3 p in
        assert_equal
          ~cmp:[%eq: string list]
          ~printer:[%show: string list]
          ["c" ^ vd]
          (consts p')
      );

    (* unints *)

    "uninterpreted instrucions of NUMBER" >:: (fun _ ->
        assert_equal
          ~cmp:[%eq: (Instruction.t * string list) list]
          ~printer:[%show: (Instruction.t * string list) list]
          [NUMBER, ["NUMBER-0"]] (Program.unints [NUMBER])
      );

    "uninterpreted instrucions of NUMBER NUMBER" >:: (fun _ ->
        assert_equal
          ~cmp:[%eq: (Instruction.t * string list) list]
          ~printer:[%show: (Instruction.t * string list) list]
          [NUMBER, ["NUMBER-0"]] (Program.unints [NUMBER; NUMBER])
      );

    "uninterpreted instrucions of SHA3" >:: (fun _ ->
        assert_equal
          ~cmp:[%eq: (Instruction.t * string list) list]
          ~printer:[%show: (Instruction.t * string list) list]
          [SHA3, ["SHA3-0-0"; "SHA3-0-1"; "SHA3-0-2"]] (Program.unints [SHA3])
      );

    "uninterpreted instrucions of SHA3 NUMBER SHA3 NUMBER" >:: (fun _ ->
        assert_equal
          ~cmp:[%eq: (Instruction.t * string list) list]
          ~printer:[%show: (Instruction.t * string list) list]
          [SHA3, ["SHA3-0-0"; "SHA3-0-1"; "SHA3-0-2"];
           NUMBER, ["NUMBER-0"];
           SHA3, ["SHA3-2-0"; "SHA3-2-1"; "SHA3-2-2"]]
          (Program.unints [SHA3; NUMBER; SHA3; NUMBER])
      );

    (* enumerate programs *)

    "enumerate programs of cost 1" >:: (fun _ ->
        let m = Int.Map.set Int.Map.empty ~key:0 ~data:[[]] in
        assert_equal ~cmp:[%eq: t list] ~printer:[%show: t list]
          [] (Tuple.T2.get1 @@ enumerate 1 Instruction.encodable m)
      );

    "enumerate programs of cost 2" >:: (fun _ ->
        let m = Int.Map.set Int.Map.empty ~key:0 ~data:[[]] in
        assert_equal ~cmp:[%eq: t list] ~printer:[%show: t list]
          [[POP]]
          (Tuple.T2.get1 @@ enumerate 2 Instruction.encodable m)
      );

    "enumerate programs of cost 3" >:: (fun _ ->
        let m = Int.Map.set Int.Map.empty ~key:0 ~data:[[]] in
        assert_equal ~cmp:[%eq: t list] ~printer:[%show: t list]
          [[ADD]; [SUB]]
          (Tuple.T2.get1 @@ enumerate 3 [ADD; SUB; POP] m)
      );

    "enumerate programs of cost 4" >:: (fun _ ->
        let m = Int.Map.set Int.Map.empty ~key:0 ~data:[[]] in
        assert_equal ~cmp:[%eq: t list] ~printer:[%show: t list]
          [[POP; POP]]
          (Tuple.T2.get1 @@ enumerate 4 [ADD; SUB; POP] m)
      );

    "enumerate programs of cost 5" >:: (fun _ ->
        let m = Int.Map.set Int.Map.empty ~key:0 ~data:[[]] in
        assert_equal ~cmp:[%eq: t list] ~printer:[%show: t list]
          [[POP; ADD]; [POP; SUB]; [ADD; POP]; [SUB; POP]]
          (Tuple.T2.get1 @@ enumerate 5 [ADD; SUB; POP] m)
      );

    "enumerate programs of cost 6" >:: (fun _ ->
        let m = Int.Map.set Int.Map.empty ~key:0 ~data:[[]] in
        assert_equal ~cmp:[%eq: t list] ~printer:[%show: t list]
          [[POP; POP; POP]; [ADD; ADD]; [SUB; ADD]; [ADD; SUB]; [SUB; SUB]]
          (Tuple.T2.get1 @@ enumerate 6 [ADD; SUB; POP] m)
      );

    "reuse map when enumerating programs of cost 6" >:: (fun _ ->
        let m = Int.Map.set Int.Map.empty ~key:0 ~data:[[]] in
        let m = Tuple.T2.get2 @@ enumerate 3 [ADD; SUB; POP] m in
        assert_equal ~cmp:[%eq: t list] ~printer:[%show: t list]
          [[POP; POP; POP]; [ADD; ADD]; [SUB; ADD]; [ADD; SUB]; [SUB; SUB]]
          (Tuple.T2.get1 @@ enumerate 6 [ADD; SUB; POP] m)
      );

  ]

let () =
  run_test_tt_main suite
