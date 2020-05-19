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
type t = {
  amnt : Z3.Expr.expr -> Z3.Expr.expr;
  decl : Z3.FuncDecl.func_decl;
}

val mk : Enc_consts.t -> string -> t

val init : t -> Z3.Expr.expr

val enc_equvivalence_at : t -> t -> Z3.Expr.expr -> Z3.Expr.expr

val enc_used_more : t -> Z3.Expr.expr -> t -> Z3.Expr.expr -> Z3.Expr.expr

val enc :Z3.Expr.expr -> Z3.Expr.expr -> Instruction.t -> t -> Z3.Expr.expr -> Z3.Expr.expr
