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

let tests =
  [

    (* check whether instruction is uninterpreted *)

    "BALANCE is an uninterpreted unary instruction" >:: (fun _ ->
        assert_bool "BALANCE is an uinterpreted instruction" (Instruction.is_uninterpreted BALANCE)
      );

    "NUMBER is an uninterpreted constant instruction" >:: (fun _ ->
        assert_bool "NUMBER is an uinterpreted instruction" (Instruction.is_uninterpreted NUMBER)
      );

    "ADD is not an uninterpreted instruction" >:: (fun _ ->
        assert_bool "ADD is not an uinterpreted instruction" (not (Instruction.is_uninterpreted ADD))
      );

    (* check whether instruction is constant *)

    "NUMBER is a constant instruction" >:: (fun _ ->
        assert_bool "NUMBER is a constant instruction" (Instruction.is_const NUMBER)
      );

    "BLOCKHASH is not a constant instruction" >:: (fun _ ->
        assert_bool "BLOCKHASH is a not constant instruction" (not (Instruction.is_const BLOCKHASH))
      );

    "BALANCE is not a constant instruction" >:: (fun _ ->
        assert_bool "BALANCE is a constant instruction" (not (Instruction.is_const BALANCE))
      );

    "SUB is not a constant instruction" >:: (fun _ ->
        assert_bool "SUB is a constant instruction" (not (Instruction.is_const SUB))
      );

    (* check arity *)

    "NUMBER has arity 0" >:: (fun _ ->
        assert_equal 0 (Instruction.arity NUMBER)
      );

    "BLOCKHASH has arity 1" >:: (fun _ ->
        assert_equal 1 (Instruction.arity BLOCKHASH)
      );

    "ADD has arity 2" >:: (fun _ ->
        assert_equal 2 (Instruction.arity ADD)
      );

  ]

let suite =
  "suite" >:::
  tests

let () =
  run_test_tt_main suite
