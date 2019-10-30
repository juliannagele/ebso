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

val to_dec : t -> string

val from_string : string -> t

val to_hex : t -> string

val numbits : t -> int

val const_to_val : t -> t

val val_to_const : t -> t

val fits_wsz : int -> t -> bool
