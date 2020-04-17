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

module PC = Program_counter

let init_rom (ea : Enc_consts.t) sk i rom =
  let open Z3Ops in
  let d = Instruction.arity i in
  let sjs = Program.poss_of_instr ea.p i in
  let tjs = Program.poss_of_instr (Option.value ~default:[] ea.tp) i in
  let js = sjs @ List.drop tjs (List.length sjs) in
  let us = Instruction.Map.find_exn ea.uis i in
  let ajs = List.map js ~f:(fun j -> Evm_stack.enc_top_d sk (PC.enc j) d) in
  let w_dflt = Word.enc_int 0 in
  let ws = List.init d ~f:(fun l -> Word.const ("w" ^ [%show: int] l)) in
  foralls ws (
    (rom @@ (Enc_consts.forall_vars ea @ ws)) ==
      List.fold_right (List.zip_exn ajs us) ~init:w_dflt
        ~f:(fun (aj, uj) enc -> ite (conj (List.map2_exn aj ws ~f:(==))) uj enc)
  )

let init (ea : Enc_consts.t) st =
  let open Z3Ops in
  Instruction.Map.fold ea.roms ~init:top ~f:(fun ~key:i ~data:f e -> e && init_rom ea st i f)

let enc_const_uninterpreted (ea : Enc_consts.t) st j i =
  let name = Instruction.unint_name 0 i in
  Evm_stack.enc_push ea.a st j (Pusharg.Word (Const name))

let enc_nonconst_uninterpreted (ea : Enc_consts.t) (sk : Evm_stack.t) j i =
  let open Z3Ops in
  let module SI = Stack_index in
  let rom = Instruction.Map.find_exn ea.roms i in
  let ajs = Evm_stack.enc_top_d sk j (Instruction.arity i) in
  (sk.el (j + one) (sk.ctr (j + one) - SI.enc 1)) == (rom @@ ((Enc_consts.forall_vars ea) @ ajs))

let enc ea sk j is =
  if Instruction.is_const is
  then enc_const_uninterpreted ea sk j is
  else enc_nonconst_uninterpreted ea sk j is
