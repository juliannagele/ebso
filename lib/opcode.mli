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

type t

type instr_map

val sort : Z3.Sort.sort

val mk_instr_map : Instruction.t list -> instr_map

val from_instr : instr_map -> Instruction.t -> t

val to_instr : instr_map -> t -> Instruction.t

val enc : t -> Z3.Expr.expr

val dec : Z3.Expr.expr -> t

val equal : t -> t -> bool

val pp : Format.formatter -> t -> unit

val show : t -> string
