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

type t = {
  el : Z3.Expr.expr -> Z3.Expr.expr -> Z3.Expr.expr;
  decl : Z3.FuncDecl.func_decl;
  ctr_decl : Z3.FuncDecl.func_decl;
  ctr : Z3.Expr.expr -> Z3.Expr.expr;
}

val mk : Enc_consts.t -> String.t -> t

val init : t -> int -> Z3.Expr.expr list -> Z3.Expr.expr

val enc_equiv_at : t -> t -> Z3.Expr.expr -> Z3.Expr.expr -> Z3.Expr.expr

val enc_top_d : t -> Z3.Expr.expr -> int -> Z3.Expr.expr list

val enc_push : Z3.FuncDecl.func_decl -> t -> Z3.Expr.expr -> Pusharg.t -> Z3.Expr.expr

val enc_pop : t -> Z3.Expr.expr -> Z3.Expr.expr

val enc_unaryop : t -> Z3.Expr.expr -> (Z3.Expr.expr -> Z3.Expr.expr) -> Z3.Expr.expr

val enc_binop : t -> Z3.Expr.expr -> (Z3.Expr.expr -> Z3.Expr.expr -> Z3.Expr.expr) -> Z3.Expr.expr

val enc_ternaryop : t -> Z3.Expr.expr -> (Z3.Expr.expr -> Z3.Expr.expr -> Z3.Expr.expr -> Z3.Expr.expr) -> Z3.Expr.expr

val enc_swap : t -> Z3.Expr.expr -> int -> Z3.Expr.expr

val enc_dup : t -> Z3.Expr.expr -> int -> Z3.Expr.expr

val pres : Instruction.t -> t -> Z3.Expr.expr -> Z3.Expr.expr

val enc_stack_ctr : Instruction.t -> t -> Z3.Expr.expr -> Z3.Expr.expr
