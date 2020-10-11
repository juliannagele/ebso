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

type t = Instruction.t list

val equal : t -> t -> bool

val t_of_sexp : Sexp.t -> t

val sexp_of_t : t -> Sexp.t

val pp_h : Format.formatter -> t -> unit

val pp_v : Format.formatter -> t -> unit

val pp_ocamllist : Format.formatter -> t -> unit

val pp_sexplist : Format.formatter -> t -> unit

val pp : Format.formatter -> t -> unit

val show_h : t -> string

val show : t -> string

val show_hex : t -> string

val cis_of_progr : t -> Instruction.t list

val stack_depth : t -> int

val total_gas_cost : t -> Gas_cost.t

val val_to_const : int -> t -> t

val const_to_val : t -> t

val consts : t -> string list

val compute_word_size : t -> int -> int

type bb = Terminal of t * Instruction.t | Next of t | NotEncodable of t

val pp_bb : Format.formatter -> bb -> unit

val show_bb : bb -> string

val equal_bb : bb -> bb -> bool

val ebso_snippet : bb -> t option

val terminal : Instruction.t list

val split_into_bbs : ?split_non_encodable:bool -> t -> bb list

val concat_bbs : bb list -> t

val enumerate : int -> Instruction.t list -> t list Int.Map.t -> t list * t list Int.Map.t

val poss_of_instr : t -> Instruction.t -> Program_counter.t list

val length : t -> Program_counter.t

val init : Program_counter.t -> f:(Program_counter.t -> 'a) -> 'a list
