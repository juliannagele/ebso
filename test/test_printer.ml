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
open OUnit2
open Printer
open Program
open Instruction

let suite =
  "suite" >:::
  [

    (* ebso snippets *)

    "Generate ebso snippet from Next" >:: (fun _ ->
        let p = [ADD; ADD; BLOCKHASH] in
        assert_equal ~cmp:[%eq: Instruction.t list option] ~printer:[%show: Instruction.t list option]
          (Some p) (ebso_snippet (Next p))
      );

    "Generate ebso snippet from Next with singleton program" >:: (fun _ ->
        let p = [ADD] in
        assert_equal ~cmp:[%eq: Instruction.t list option] ~printer:[%show: Instruction.t list option]
          (Some p) (ebso_snippet (Next p))
      );

    "Generate ebso snippet from Terminal" >:: (fun _ ->
        let p = [ADD; ADD; BLOCKHASH] in
        assert_equal ~cmp:[%eq: Instruction.t list option] ~printer:[%show: Instruction.t list option]
          (Some p) (ebso_snippet (Terminal(p, STOP)))
      );

    "Generate ebso snippet from Terminal with singleton program" >:: (fun _ ->
        let p = [ADD] in
        assert_equal ~cmp:[%eq: Instruction.t list option] ~printer:[%show: Instruction.t list option]
          (Some p) (ebso_snippet (Terminal (p, STOP)))
      );

    "Generate ebso snippet from not encodable instruction" >:: (fun _ ->
        let p = [LOG0; LOG0] in
        assert_equal ~cmp:[%eq: Instruction.t list option] ~printer:[%show: Instruction.t list option]
          None (ebso_snippet (NotEncodable p))
      );

    (* show ebso snippet *)

    "Show a simple ebso snippet" >:: (fun _ ->
        let s = [ADD; ADD] in
        assert_equal ~cmp:[%eq: string list] ~printer:[%show: string list]
          ["0101"; "ADD ADD"; "2"; "3"; "0"; "0"]
          (show_ebso_snippet s)
      );

    "Show a complicated ebso snippet" >:: (fun _ ->
        let s = [SSTORE; SLOAD; ADD; BLOCKHASH; BLOCKHASH; NUMBER] in
        assert_equal ~cmp:[%eq: string list] ~printer:[%show: string list]
          ["555401404043"; "SSTORE SLOAD ADD BLOCKHASH BLOCKHASH NUMBER"; "6"; "4"; "3"; "2"]
          (show_ebso_snippet s)
      );

    (* show result *)

    "Show a result" >:: (fun _ ->
        let s = [PUSH (Val "1"); POP] in
        let t = [] in
        let step = {input = s; opt = t; optimal = true; tval = None} in
        assert_equal ~cmp:[%eq: string list] ~printer:[%show: string list]
          ["600150"; ""; ""; "0"; "5"; "0"; "5"; "true";]
          (show_result step)
      );

    "Show a result with failed translation validation" >:: (fun _ ->
        let s = [NOT; ADD] in
        let t = [EQ] in
        let step = {input = s; opt = t; optimal = true; tval = Some false} in
        assert_equal ~cmp:[%eq: string list] ~printer:[%show: string list]
          ["1901"; "14"; "EQ"; "1"; "6"; "3"; "3"; "true"; "false"]
          (show_result step)
      );

    "Show a result with a successful translation validation" >:: (fun _ ->
        let s = [PUSH (Val "0"); ADD; POP] in
        let t = [POP] in
        let step = {input = s; opt = t; optimal = true; tval = Some true} in
        assert_equal ~cmp:[%eq: string list] ~printer:[%show: string list]
          ["60000150"; "50"; "POP"; "1"; "8"; "2"; "6"; "true"; "true"]
          (show_result step)
      );

    "Show a result with SSTORE" >:: (fun _ ->
        let s = [PUSH (Val "1"); DUP II; SWAP I; SSTORE; PUSH (Val "1"); DUP II; SWAP I; SSTORE; POP; POP] in
        let t = [PUSH (Val "1"); SSTORE; POP] in
        let step = {input = s; opt = t; optimal = false; tval = Some true} in
        assert_equal ~cmp:[%eq: string list] ~printer:[%show: string list]
          ["600181905560018190555050"; "60015550"; "PUSH 1 SSTORE POP"; "3"; "tbc"; "tbc"; "tbc"; "false"; "true"]
          (show_result step)
      );
  ]

let () =
  run_test_tt_main suite
