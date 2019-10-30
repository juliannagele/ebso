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
open Instruction
open Program

module PC = Program_counter

let suite =
  "suite" >:::
  [
    (* stack_depth *)

    "No negative stack depth, sufficient arguments" >::(fun _ ->
        let p = [PUSH (Word (Val "1")); PUSH (Word (Val "1")); PUSH (Word (Val "1")); SUB] in
        assert_equal ~cmp:[%eq: int] ~printer:[%show: int]
          0 (stack_depth p)
      );

    "Stack depth of SUB" >::(fun _ ->
        let p = [SUB] in
        assert_equal ~cmp:[%eq: int] ~printer:[%show: int]
          2 (stack_depth p)
      );

    "Stack depth of exactly enough arguments" >::(fun _ ->
        let p = [PUSH (Word (Val "1")); PUSH (Word (Val "1")); SUB] in
        assert_equal ~cmp:[%eq: int] ~printer:[%show: int]
          0 (stack_depth p)
      );

    "Stack depth when starting with SUB, go positive, but then go deeper" >::(fun _ ->
        let p = [SUB; PUSH (Word (Val "1")); PUSH (Word (Val "1")); ADD; ADD; ADD] in
        assert_equal ~cmp:[%eq: int] ~printer:[%show: int]
          3 (stack_depth p)
      );

    (* cis_of_progr / Instruction.all *)

    "compute instruction set of given program" >::(fun _ ->
        let p = [SUB; PUSH (Word (Val "1")); PUSH (Word (Val "1")); ADD; ADD; PUSH (Word (Val "2")); POP] in
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
          [OR; ADD; SWAP I; JUMPDEST; LOG1; POP; JUMP; DUP III;
           PUSH (Word (Val "0")); ISZERO; JUMPI; POP; RETURN]
        in
        assert_equal ~cmp:[%eq: Program.bb list] ~printer:[%show: Program.bb list]
          [Next [OR; ADD; SWAP I]; Terminal ([JUMPDEST; LOG1; POP], JUMP);
           Terminal ([DUP III; PUSH (Word (Val "0")); ISZERO], JUMPI);
           Terminal ([POP], RETURN)]
          (split_into_bbs ~split_non_encodable:false p)
      );

    "splitting a program into BBs and then concatenating them back" >::(fun _ ->
        let p =
          [OR; ADD; SWAP I; JUMPDEST; LOG1; POP; JUMP; DUP III;
           PUSH (Word (Val "0")); ISZERO; JUMPI; POP; RETURN]
        in
        assert_equal ~cmp:[%eq: Program.t] ~printer:[%show: Program.t]
          p
          (concat_bbs @@ split_into_bbs ~split_non_encodable:false p)
      );

    "split program at non-encodable instructions" >::(fun _ ->
        let p =
          [OR; ADD; SWAP I; JUMPDEST; LOG1; POP; JUMP; DUP III;
           PUSH (Word (Val "0")); ISZERO; JUMPI; POP; RETURN]
        in
        assert_equal ~cmp:[%eq: Program.bb list] ~printer:[%show: Program.bb list]
          [Next [OR; ADD; SWAP I]; NotEncodable [JUMPDEST; LOG1];
           Terminal ([POP], JUMP);
           Terminal ([DUP III; PUSH (Word (Val "0")); ISZERO], JUMPI);
           Terminal ([POP], RETURN)]
          (split_into_bbs p)
      );

    "splitting into BBs and concatenating back with non-encodable split" >::(fun _ ->
        let p =
          [OR; ADD; SWAP I; JUMPDEST; LOG1; POP; JUMP; DUP III;
           PUSH (Word (Val "0")); ISZERO; JUMPI; POP; RETURN]
        in
        assert_equal ~cmp:[%eq: Program.t] ~printer:[%show: Program.t]
          p
          (concat_bbs @@ split_into_bbs p)
      );

    (* val_to_const *)

    "replace large val with const" >:: (fun _ ->
        let v = "16" in
        let wsz = 2 in
        let p = [PUSH (Word (Val v))] in
        assert_equal
          ~cmp:[%eq: Program.t]
          ~printer:[%show: Program.t]
          [PUSH (Word (Const ("c" ^ v)))]
          (val_to_const wsz p)
      );

    "do not replace fitting val with const" >:: (fun _ ->
        let v = "1" in
        let wsz = 2 in
        let p = [PUSH (Word (Val v))] in
        assert_equal
          ~cmp:[%eq: Program.t]
          ~printer:[%show: Program.t]
          [PUSH (Word (Val v))]
          (val_to_const wsz p)
      );

    "do not replace 0 with const" >:: (fun _ ->
        let v = "0" in
        let wsz = 2 in
        let p = [PUSH (Word (Val v))] in
        assert_equal
          ~cmp:[%eq: Program.t]
          ~printer:[%show: Program.t]
          [PUSH (Word (Val v))]
          (val_to_const wsz p)
      );

    "replace in program" >:: (fun _ ->
        let wsz = 2 in
        let p = [PUSH (Word (Val "2")); PUSH (Word (Val "17")); PUSH (Word (Val "9")); ADD; PUSH (Word (Val "100"))] in
        assert_equal
          ~cmp:[%eq: Program.t]
          ~printer:[%show: Program.t]
          [PUSH (Word (Val "2")); PUSH (Word (Const "c17")); PUSH (Word (Const "c9")); ADD; PUSH (Word (Const "c100"))]
          (val_to_const wsz p)
      );

    "replace same value in program" >:: (fun _ ->
        let v = "42" in
        let wsz = 2 in
        let p = [PUSH (Word (Val v)); PUSH (Word (Val v))] in
        assert_equal
          ~cmp:[%eq: Program.t]
          ~printer:[%show: Program.t]
          [PUSH (Word (Const ("c" ^ v))); PUSH (Word (Const ("c" ^ v)))]
          (val_to_const wsz p)
      );

    "replace max value and max + 1 in program" >:: (fun _ ->
        let max = "3" in
        let max_1 = "4" in
        let wsz = 2 in
        let p = [PUSH (Word (Val max)); PUSH (Word (Val max_1))] in
        assert_equal
          ~cmp:[%eq: Program.t]
          ~printer:[%show: Program.t]
          [PUSH (Word (Val max)); PUSH (Word (Const ("c" ^ max_1)))]
          (val_to_const wsz p)
      );

    "replace large binary val with const" >:: (fun _ ->
        let v = "0b1001" in
        let wsz = 2 in
        let p = [PUSH (Word (Val v))] in
        assert_equal
          ~cmp:[%eq: Program.t]
          ~printer:[%show: Program.t]
          [PUSH (Word (Const ("c9")))]
          (val_to_const wsz p)
      );

    (* const_to_val *)

    "redeem val from const" >:: (fun _ ->
        let v = "42" in
        let p = [PUSH (Word (Const ("c" ^ v)))] in
        assert_equal
          ~cmp:[%eq: Program.t]
          ~printer:[%show: Program.t]
          [PUSH (Word (Val v))]
          (const_to_val p)
      );

    "redeem large binary val from const" >:: (fun _ ->
        let v = "0b1001" in
        let p = [PUSH (Word (Const ("c" ^ v)))] in
        assert_equal
          ~cmp:[%eq: Program.t]
          ~printer:[%show: Program.t]
          [PUSH (Word (Val v))]
          (const_to_val p)
      );

    "idempotent with fitting value" >:: (fun _ ->
        let v = "1" in
        let wsz = 2 in
        let p = [PUSH (Word (Val v))] in
        assert_equal
          ~cmp:[%eq: Program.t]
          ~printer:[%show: Program.t]
          p
          (const_to_val (val_to_const wsz p))
      );

    "idempotent in large program" >:: (fun _ ->
        let wsz = 2 in
        let p = [PUSH (Word (Val "2")); PUSH (Word (Val "17")); PUSH (Word (Val "9")); ADD; PUSH (Word (Val "100"))] in
        assert_equal
          ~cmp:[%eq: Program.t]
          ~printer:[%show: Program.t]
          p
          (const_to_val (val_to_const wsz p))
      );

    "idempotent with same value in program" >:: (fun _ ->
        let v = "42" in
        let wsz = 2 in
        let p = [PUSH (Word (Val v)); PUSH (Word (Val v))] in
        assert_equal
          ~cmp:[%eq: Program.t]
          ~printer:[%show: Program.t]
          p
          (const_to_val (val_to_const wsz p))
      );

    (* consts *)

    "get constants from program" >:: (fun _ ->
        let c1 = "c123" and c2 = "c321" in
        let p = [PUSH (Word (Val "2")); PUSH (Word (Const c1)); PUSH (Word (Const c1)); PUSH (Word (Const c2))] in
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
        let p = [PUSH (Word (Val vb)); PUSH (Word (Val vd)); PUSH (Word (Val vh));] in
        let p' = Program.val_to_const 3 p in
        assert_equal
          ~cmp:[%eq: string list]
          ~printer:[%show: string list]
          ["c" ^ vd]
          (consts p')
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
          [[ADD; POP]; [SUB; POP]]
          (Tuple.T2.get1 @@ enumerate 5 [ADD; SUB; POP] m)
      );

    "enumerate programs of cost 6" >:: (fun _ ->
        let m = Int.Map.set Int.Map.empty ~key:0 ~data:[[]] in
        assert_equal ~cmp:[%eq: t list] ~printer:[%show: t list]
          [[POP; POP; POP]; [ADD; ADD]; [ADD; SUB]; [SUB; SUB]]
          (Tuple.T2.get1 @@ enumerate 6 [ADD; SUB; POP] m)
      );

    "reuse map when enumerating programs of cost 6" >:: (fun _ ->
        let m = Int.Map.set Int.Map.empty ~key:0 ~data:[[]] in
        let m = Tuple.T2.get2 @@ enumerate 3 [ADD; SUB; POP] m in
        assert_equal ~cmp:[%eq: t list] ~printer:[%show: t list]
          [[POP; POP; POP]; [ADD; ADD]; [ADD; SUB]; [SUB; SUB]]
          (Tuple.T2.get1 @@ enumerate 6 [ADD; SUB; POP] m)
      );

    (* compute word size, trying to minimize number of allquantified bits *)

    "without any values, use word-size 1" >:: (fun _ ->
        assert_equal ~cmp:[%eq: int] ~printer:[%show: int]
          1 (compute_word_size [ADDRESS; ADD; POP; SUB] 256)
      );

    "without any input variables, use word-size to fit all values" >:: (fun _ ->
        assert_equal ~cmp:[%eq: int] ~printer:[%show: int]
          3 (compute_word_size [PUSH (Word (Val "5")); PUSH (Word (Val "2")); ADD] 256)
      );

    "tie-breaker: fit value" >:: (fun _ ->
        assert_equal ~cmp:[%eq: int] ~printer:[%show: int]
          2 (compute_word_size [PUSH (Word (Val "2")); ADD] 256)
      );

    "abstracting value yields fewer allquantified bits" >:: (fun _ ->
        assert_equal ~cmp:[%eq: int] ~printer:[%show: int]
          1 (compute_word_size [PUSH (Word (Val "5")); ADD] 256)
      );

    "fitting values yields fewer allquantified bits" >:: (fun _ ->
        assert_equal ~cmp:[%eq: int] ~printer:[%show: int]
          2 (compute_word_size [ADD; PUSH (Word (Val "3")); PUSH (Word (Val "3")); PUSH (Word (Val "3"))] 256)
      );

    "fitting some values and abstracting another" >:: (fun _ ->
        assert_equal ~cmp:[%eq: int] ~printer:[%show: int]
          2 (compute_word_size [ADD; PUSH (Word (Val "3")); PUSH (Word (Val "3")); PUSH (Word (Val "3")); PUSH (Word (Val "40"))] 256)
      );

    "uninterpreted instruction needs a variable" >:: (fun _ ->
        assert_equal ~cmp:[%eq: int] ~printer:[%show: int]
          1 (compute_word_size [PUSH (Word (Val "2")); EXP] 256)
      );

    "tie-breaker with uninterpreted instruction" >:: (fun _ ->
        assert_equal ~cmp:[%eq: int] ~printer:[%show: int]
          2 (compute_word_size [ADDRESS; PUSH (Word (Val "2"))] 256)
      );

    "uninterpreted instruction results in abstracting value" >:: (fun _ ->
        assert_equal ~cmp:[%eq: int] ~printer:[%show: int]
          1 (compute_word_size [BLOCKHASH; PUSH (Word (Val "2"))] 256)
      );

    "fitting some values and abstracting another" >:: (fun _ ->
        assert_equal ~cmp:[%eq: int] ~printer:[%show: int]
          2 (compute_word_size [BLOCKHASH; PUSH (Word (Val "3")); PUSH (Word (Val "3")); PUSH (Word (Val "3")); PUSH (Word (Val "40"))] 256)
      );


    (* pos *)

    "get position of instruction BALANCE" >:: (fun _ ->
        assert_equal ~cmp:[%eq: PC.t list]  ~printer:[%show: PC.t list]
          [PC.of_int 0; PC.of_int 2] (poss_of_instr [BALANCE; POP; BALANCE] BALANCE)
      );

    "get position of instruction BALANCE" >:: (fun _ ->
        assert_equal ~cmp:[%eq: PC.t list]  ~printer:[%show: PC.t list]
          [] (poss_of_instr [POP; POP] BALANCE);
      );
  ]

let () =
  run_test_tt_main suite
