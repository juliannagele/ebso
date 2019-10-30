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

(* a value argument can be either decimal, e.g., "1", hex, e.g., "0x1"
   or binary, e.g. "0b1" *)
type t = Val of string [@@deriving show { with_path = false }, sexp, compare]

let size = ref 3

let sort = ref (bv_sort !size)

let set_wsz n = size := n; sort := bv_sort !size

let enc_int n = Z3.Expr.mk_numeral_int !ctxt n !sort

let enc_string n = Z3.Expr.mk_numeral_string !ctxt n !sort

let const s = Z3.Expr.mk_const_s !ctxt s !sort

let to_hex = function
  | Val x ->  Z.of_string x |> Z.format "x"

let to_dec = function
  | Val x -> Z.of_string x |> Z.to_string

let equal x y = match x, y with
  | Val x, Val y -> Z.equal (Z.of_string x) (Z.of_string y)

let show_hex x =
    let hx = to_hex x in
    if Int.rem (String.length hx) 2 = 1 then "0" ^ hx else hx

let const_to_val c =
  let x =
    try String.chop_prefix_exn c ~prefix:"c"
    with _ -> failwith "Cannot convert " ^ c ^ " into value"
  in Val x

let val_to_const x = "c" ^ (to_dec x)

let from_string x = Val x

let numbits x = Z.numbits (Z.of_string (to_dec x))
