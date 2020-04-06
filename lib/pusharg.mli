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

type t = Word of Word.t | Tmpl

val pp : Format.formatter -> t -> unit

val show : t -> string

val t_of_sexp : Sexp.t -> t

val sexp_of_t : t -> Sexp.t

val compare : t -> t -> int

val equal : t -> t -> bool

val all : t list

val show_hex : t -> string

val enc : Z3.FuncDecl.func_decl -> Z3.Expr.expr -> t -> Z3.Expr.expr
