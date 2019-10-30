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
open Z3util

type t =
  | Word of Word.t [@printer fun fmt x -> fprintf fmt "%s" (Word.to_dec x)]
  | Tmpl
[@@deriving show { with_path = false }, sexp, compare]

let equal x y = match (x, y) with
  | Word w1, Word w2 -> Word.equal w1 w2
  | Tmpl, Tmpl -> true
  | _, _ -> false

let of_sexp s = match s with
  | Sexp.Atom i -> if String.equal i "Tmpl" then Tmpl else Word (Word.from_string i)
  | Sexp.List _ -> failwith "could not parse argument of PUSH"

let all = [Tmpl]

let show_stackarg_hex a =
  match a with
  | Word x -> Word.show_hex x
  | Tmpl -> failwith "hex output not supported for template"

let val_to_const wsz a =
  let max_repr = Z.pow (Z.of_int 2) wsz in
  match a with
  | Word (Val x) when Z.of_string (Word.to_dec (Val x)) >= max_repr -> Word (Word.val_to_const (Val x))
  | a -> a

let const_to_val = function
  | Word (Const c) -> Word (Word.const_to_val (Const c))
  | a -> a

(* careful: if x is to large for Word.sort leftmost bits are truncated *)
let enc x =
  Z3.Expr.mk_numeral_string !ctxt (Word.to_dec x) !Word.sort
