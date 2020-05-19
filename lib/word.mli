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

type t = Val of string | Const of string

val size : int ref

val sort : Z3.Sort.sort ref

val set_wsz : int -> unit

val enc_int : int -> Z3.Expr.expr

val const : string -> Z3.Expr.expr

val enc : t -> Z3.Expr.expr

val show : t -> string

val show_hex : t -> string

val pp : Format.formatter -> t -> unit

val t_of_sexp : Sexplib.Sexp.t -> t

val sexp_of_t : t -> Sexplib.Sexp.t

val equal : t -> t -> bool

val compare : t -> t -> int

val from_string : string -> t

val numbits : t -> int

val to_val : t -> t

val to_const : t -> t

val fits_wsz : int -> t -> bool

val enc_add : Z3.Expr.expr -> Z3.Expr.expr -> Z3.Expr.expr

val enc_sub : Z3.Expr.expr -> Z3.Expr.expr -> Z3.Expr.expr

val enc_mul : Z3.Expr.expr -> Z3.Expr.expr -> Z3.Expr.expr

val enc_div : Z3.Expr.expr -> Z3.Expr.expr -> Z3.Expr.expr

val enc_sdiv : Z3.Expr.expr -> Z3.Expr.expr -> Z3.Expr.expr

val enc_mod : Z3.Expr.expr -> Z3.Expr.expr -> Z3.Expr.expr

val enc_smod : Z3.Expr.expr -> Z3.Expr.expr -> Z3.Expr.expr

val enc_lt : Z3.Expr.expr -> Z3.Expr.expr -> Z3.Expr.expr

val enc_gt : Z3.Expr.expr -> Z3.Expr.expr -> Z3.Expr.expr

val enc_slt : Z3.Expr.expr -> Z3.Expr.expr -> Z3.Expr.expr

val enc_sgt : Z3.Expr.expr -> Z3.Expr.expr -> Z3.Expr.expr

val enc_eq : Z3.Expr.expr -> Z3.Expr.expr -> Z3.Expr.expr

val enc_and : Z3.Expr.expr -> Z3.Expr.expr -> Z3.Expr.expr

val enc_or : Z3.Expr.expr -> Z3.Expr.expr -> Z3.Expr.expr

val enc_xor : Z3.Expr.expr -> Z3.Expr.expr -> Z3.Expr.expr

val enc_addmod : Z3.Expr.expr -> Z3.Expr.expr -> Z3.Expr.expr -> Z3.Expr.expr

val enc_mulmod : Z3.Expr.expr -> Z3.Expr.expr -> Z3.Expr.expr -> Z3.Expr.expr

val enc_not : Z3.Expr.expr -> Z3.Expr.expr

val enc_iszero : Z3.Expr.expr -> Z3.Expr.expr
