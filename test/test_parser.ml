open Core
open OUnit2
open Instruction
open Sedlexing
open Parser

let suite =
  "suite" >:::
  [
    "parse_idx 10" >:: (fun _ ->
        assert_equal ~cmp:[%eq: idx] ~printer:[%show: idx]
          X (parse_idx "SWAP" "SWAP10")
      );

    "parse_idx 1" >:: (fun _ ->
        assert_equal ~cmp:[%eq: idx] ~printer:[%show: idx]
          I (parse_idx "SWAP" "SWAP1")
      );

    "parse_idx fail 17" >:: (fun _ ->
        assert_raises (Info.to_exn @@ Info.of_string @@ "parse SWAP index failed")
          (fun () -> parse_idx "SWAP" "SWAP17")
      );

    "parse_idx fail -1" >:: (fun _ ->
        assert_raises (Info.to_exn @@ Info.of_string @@ "parse SWAP index failed")
          (fun () -> parse_idx "SWAP" "SWAP-1")
      );

    "parse_idx fail a" >:: (fun _ ->
        assert_raises (Failure "Int.of_string: \"a\"")
          (fun () -> parse_idx "SWAP" "SWAPa")
      );

    "parse instruction list" >:: (fun _ ->
        let s = List.to_string ~f:Instruction.show Instruction.encodable in
        let buf = Latin1.from_string s in
        assert_equal ~cmp:[%eq: Instruction.t list] ~printer:[%show: Instruction.t list]
          Instruction.encodable
          (parse buf)
      );

    "parse instruction list fail B" >:: (fun _ ->
        let buf = Latin1.from_string "ADD B SWAP1" in
        assert_raises (SyntaxError 4)
          (fun () -> parse buf)
      );
  ]

let () =
  run_test_tt_main suite
