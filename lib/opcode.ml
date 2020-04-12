(*   Copyright 2019 Julian Nagele and Maria A Schett

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
open Z3util

type t = Z.t [@@deriving eq]

type instr_map = (Instruction.t * t) list

let show = Z.to_string

let pp fmt n = Format.fprintf fmt "%s" (show n)

let sort = int_sort

let mk_instr_map = List.mapi ~f:(fun i oc -> (oc, (Z.of_int i)))

let from_instr ops i = List.Assoc.find_exn ops ~equal:[%eq: Instruction.t] i

let to_instr ops i =
  List.Assoc.find_exn (List.Assoc.inverse ops) ~equal:[%eq: t] i

let enc = num

let dec e = Z3.Arithmetic.Integer.get_big_int e |> Big_int.string_of_big_int |> Z.of_string
