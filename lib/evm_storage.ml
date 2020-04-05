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
module SI = Stack_index

type t = {
  el : Z3.Expr.expr -> Z3.Expr.expr -> Z3.Expr.expr;
  decl : Z3.FuncDecl.func_decl;
}

let mk ea idx =
  let mk_vars_sorts vs = List.map vs ~f:(fun _ -> !Word.sort) in
  let vars_sorts = mk_vars_sorts (Enc_consts.forall_vars ea) in
  let str = func_decl ("storage" ^ idx) (vars_sorts @ [PC.sort; !Word.sort]) !Word.sort in
  {
    (* storage(_, j, k) = v if storage after j instructions contains word v for key k *)
    decl = str;
    el = (fun j w -> str <@@> (Enc_consts.forall_vars ea @ [j; w]));
  }

let init str sk js ss =
  let open Z3Ops in
  let ks = List.concat_map js ~f:(fun j -> Evm_stack.enc_top_d sk (PC.enc j) 1) in
  let w_dflt = Word.enc_int 0 in
  let w = Word.const "w" in
  forall w (
    (str.el PC.init w ==
     List.fold_right (List.zip_exn ks ss) ~init:w_dflt
       ~f:(fun (k, s) enc -> ite (w == k) s enc)))

let enc_equiv_at strs strt js jt =
  let open Z3Ops in
  let w = Word.const "w" in
  (* source and target storage are equal *)
  forall w ((strs.el js w) == (strt.el jt w))

let enc_sload str sk j = Evm_stack.enc_unaryop sk j (str.el j)

let enc_sstore str sk j =
  let open Z3Ops in
  let sc = let open Evm_stack in sk.ctr j in
  let sk = let open Evm_stack in sk.el in
  let w = Word.const "w" in
  forall w (str.el (j + one) w ==
            (ite (w == sk j (sc - SI.enc 1)) (sk j (sc - SI.enc 2)) (str.el j w)))

let pres is str j =
  let open Z3Ops in
  match is with
  | Instruction.SSTORE -> top
  | _ -> let w = Word.const "w" in forall w (str.el (j + one) w == str.el j w)
