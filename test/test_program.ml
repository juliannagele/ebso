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

    (* sis_of_progr / Instruction.all *)

    "compute instruction set of given program" >::(fun _ ->
        let p = [SUB; PUSH (Val "1"); PUSH (Val "1"); ADD; ADD; PUSH (Val "2"); POP] in
        assert_equal ~cmp:[%eq: Program.t] ~printer:[%show: Program.t]
          [SUB; PUSH Tmpl; ADD; POP] (sis_of_progr p)
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

    (* mod_to_ses *)

    "stack elements is modulo-ed" >::(fun _ ->
        let p = [PUSH (Val "17"); PUSH (Val "-9"); PUSH (Val "0x12")] in
        assert_equal ~cmp:[%eq: Program.t] ~printer:[%show: Program.t]
          [PUSH (Val "1"); PUSH (Val "9"); PUSH (Val "2")]
          (mod_to_ses 4 p)
      );

    "stack elements are small enough" >::(fun _ ->
        let p = [PUSH (Val "1"); PUSH (Val "0")] in
        assert_equal ~cmp:[%eq: Program.t] ~printer:[%show: Program.t]
          p
          (mod_to_ses 4 p)
      );

    "program without PUSH remains unchanged by mod_to_ses" >:: (fun _ ->
        let p = [ADD; SUB; EXP] in
        assert_equal ~cmp:[%eq: Program.t] ~printer:[%show: Program.t]
        p
        (mod_to_ses 4 p)
      );

    (* val_to_const *)

    "replace large val with const" >:: (fun _ ->
        let p = [PUSH (Val "0b1011")] in
        assert_equal
          ~cmp:[%eq: Program.t * const_val_map]
          ~printer:[%show: Program.t * const_val_map]
          (val_to_const 2 p)
          ([PUSH (Const "c1")], [("c1", "0b1011")])
      );


  ]

let () =
  run_test_tt_main suite
