(*   Copyright 2020 Julian Nagele and Maria A Schett

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
module SI = Stack_index

type t = {
  in_exc_halt : Z3.Expr.expr -> Z3.Expr.expr;
  decl : Z3.FuncDecl.func_decl;
}

let mk _ idx =
  let eh = func_decl ("exc_halt" ^ idx) [PC.sort] bool_sort; in
  {
    decl = eh;
    in_exc_halt = (fun j -> eh <@@> [j]);
  }

let init eh =
  let open Z3Ops in
  eh.in_exc_halt PC.init == btm

let enc_equiv_at ehs eht js jt =
  let open Z3Ops in
  ehs.in_exc_halt js == eht.in_exc_halt jt

let enc sc is eh j =
  let (d, a) = Instruction.delta_alpha is in let diff = (a - d) in
  let open Z3Ops in
  let underflow = if Int.is_positive d then (sc - (SI.enc d)) < (SI.enc 0) else btm in
  let overflow =
    if Int.is_positive diff then
      match Z3.Sort.get_sort_kind !SI.sort with
      | BV_SORT -> ~! (nuw sc (SI.enc diff) `Add)
      | INT_SORT -> (sc + (SI.enc diff)) > (SI.enc 1024)
      | _ -> btm
    else btm
  in
  eh.in_exc_halt (j + one) == (eh.in_exc_halt j || underflow || overflow)
