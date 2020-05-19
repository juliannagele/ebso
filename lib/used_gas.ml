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
module GC = Gas_cost

type t = {
  amnt : Z3.Expr.expr -> Z3.Expr.expr;
  decl : Z3.FuncDecl.func_decl;
}

let mk ea idx =
  let mk_vars_sorts vs = List.map vs ~f:(fun _ -> !Word.sort) in
  let vars_sorts = mk_vars_sorts (Enc_consts.forall_vars ea) in
  let ug = func_decl ("used_gas" ^ idx) (vars_sorts @ [PC.sort]) GC.sort in
  {
    decl = ug;
    amnt = (fun j -> ug <@@> (Enc_consts.forall_vars ea @ [j]));
  }

let init ug =
  let open Z3Ops in
   (ug.amnt PC.init == GC.enc GC.zero)

let enc_equvivalence_at ugs ugt j =
  let open Z3Ops in
  ugs.amnt PC.init == ugt.amnt j

let enc_used_more ugs ks ugt kt =
  let open Z3Ops in
  ugs.amnt ks > ugt.amnt kt

let enc v v' is ug  j =
  let open Z3Ops in
  let cost =
    let refund = GC.enc (GC.of_int 15000)
    and set = GC.enc (GC.of_int 20000)
    and reset = GC.enc (GC.of_int 5000) in
    match is with
    | Instruction.T.SSTORE ->
      ite (v == Word.enc_int 0)
        (ite (v' == Word.enc_int 0) reset set)
        (ite (v' == Word.enc_int 0) (reset - refund) reset)
    | _ -> GC.enc (Instruction.gas_cost is)
  in
  ug.amnt (j + one) == (ug.amnt j + cost)
