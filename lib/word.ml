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
type t = Val of string [@printer fun fmt x -> fprintf fmt "%s" x]
       | Const of string [@printer fun fmt x -> fprintf fmt "c%s" x]
[@@deriving show { with_path = false }, sexp, compare]

let size = ref 3

let sort = ref (bv_sort !size)

let to_val w = match w with
  | Const c -> Val c
  | w -> w

let set_wsz n = size := n; sort := bv_sort !size

let rec to_hex = function
  | Val x ->  Z.of_string x |> Z.format "x"
  | Const c -> to_hex (to_val (Const c))

let rec to_dec = function
  | Val x -> Z.of_string x |> Z.to_string
  | Const c -> to_dec (to_val (Const c)) (* convention is that constarg is in dec *)

let enc_int n = Z3.Expr.mk_numeral_int !ctxt n !sort

let const s = Z3.Expr.mk_const_s !ctxt s !sort

let enc = function
  | Const c -> const c
  (* careful: if x is to large for Word.sort leftmost bits are truncated *)
  | Val x ->
    let enc_string n = Z3.Expr.mk_numeral_string !ctxt n !sort in
    enc_string (to_dec (Val x))

let equal w1 w2 = match w1, w2 with
  | Val x, Val y -> Z.equal (Z.of_string x) (Z.of_string y)
  | Const c, Const d -> String.equal c d
  | _ -> false

let show_hex x =
    let hx = to_hex x in
    if Int.rem (String.length hx) 2 = 1 then "0" ^ hx else hx

let to_const w = match w with
  | Val x -> Const (to_dec (Val x))
  | _ -> w

let from_string x = match String.chop_prefix x ~prefix:"c" with
  | Some c ->  Const c
  | None -> Val x

let numbits x = Z.numbits (Z.of_string (to_dec x))

let fits_wsz wsz = function
  | Const _ -> true
  | w ->
    let max_repr = Z.pow (Z.of_int 2) wsz in
    Z.lt (Z.of_string (to_dec w)) max_repr

let enc_add = (<+>)
let enc_sub = (<->)
let enc_mul = (<*>)

let enc_div num denom =
  (* EVM defines x / 0 = 0, Z3 says it's undefined *)
  ite (denom <==> enc_int 0) (enc_int 0) (udiv num denom)

let enc_sdiv num denom =
  (* EVM defines x / 0 = 0, Z3 says it's undefined *)
  ite (denom <==> enc_int 0) (enc_int 0) (sdiv num denom)

let enc_mod num denom =
  (* EVM defines x mod 0 = 0, Z3 says it's undefined *)
  ite (denom <==> enc_int 0) (enc_int 0) (urem num denom)

let enc_smod num denom =
  (* Z3 has srem and smod; srem takes sign from dividend (= num),
     smod from divisor (= denom); EVM takes the latter *)
  (* EVM defines x smod 0 = 0, Z3 says it's undefined *)
  ite (denom <==> enc_int 0) (enc_int 0) (srem num denom)

let enc_lt x y = ite (Z3.BitVector.mk_ult !ctxt x y) (enc_int 1) (enc_int 0)

let enc_gt x y = ite (Z3.BitVector.mk_ugt !ctxt x y) (enc_int 1) (enc_int 0)

let enc_slt x y = ite (x <<> y) (enc_int 1) (enc_int 0)

let enc_sgt x y = ite (x <>> y) (enc_int 1) (enc_int 0)

let enc_eq x y = ite (x <==> y) (enc_int 1) (enc_int 0)

let enc_and = Z3.BitVector.mk_and !ctxt
let enc_or = Z3.BitVector.mk_or !ctxt
let enc_xor = Z3.BitVector.mk_xor !ctxt

let enc_addmod x y denom =
  let open Z3Ops in
  (* EVM defines (x + y) mod 0 = 0 as 0, Z3 says it's undefined *)
  ite (denom == enc_int 0) (enc_int 0) (
    (* truncate back to word size, safe because mod denom brings us back to range *)
    extract (Int.pred !size) 0
      (* requires non overflowing add, pad with 0s to avoid overflow *)
      (urem ((zeroext 1 x) + (zeroext 1 y)) (zeroext 1 denom)))

let enc_mulmod x y denom =
  let open Z3Ops in
  (* EVM defines (x + y) mod 0 = 0 as 0, Z3 says it's undefined *)
  ite (denom == enc_int 0) (enc_int 0) (
    (* truncate back to word size, safe because mod denom brings us back to range *)
    extract (Int.pred !size) 0
      (* requires non overflowing mul, pad with 0s to avoid overflow *)
      (urem ((zeroext !size x) * (zeroext !size y)) (zeroext !size denom)))

let enc_not = Z3.BitVector.mk_not !ctxt

let enc_iszero w =
  let open Z3Ops in
  ite (w == (enc_int 0)) (enc_int 1) (enc_int 0)
