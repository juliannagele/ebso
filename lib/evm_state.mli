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
  stack : Evm_stack.t;
  storage : Evm_storage.t;
  exc_halt : Exc_halt.t;
  used_gas : Used_gas.t;
}

val mk : Enc_consts.t -> string -> t

val init : Enc_consts.t -> t -> Z3.Expr.expr

val enc_instruction : Enc_consts.t -> t -> Z3.Expr.expr -> Instruction.t -> Z3.Expr.expr

val enc_program : Enc_consts.t -> t -> Z3.Expr.expr

val enc_equiv_at : t -> t -> Z3.Expr.expr -> Z3.Expr.expr -> Z3.Expr.expr

val enc_equiv : Enc_consts.t -> t -> t -> Z3.Expr.expr

val eval_stack : ?xs:Z3.Expr.expr list -> t -> Z3.Model.model -> Program_counter.t -> int -> Z3.Expr.expr

val eval_stack_ctr : t -> Z3.Model.model -> Program_counter.t -> Z3.Expr.expr

val eval_storage : ?xs:Z3.Expr.expr list -> t -> Z3.Model.model -> Program_counter.t -> Z3.Expr.expr -> Z3.Expr.expr

val eval_exc_halt : t -> Z3.Model.model -> Program_counter.t -> Z3.Expr.expr

val eval_gas : ?xs:Z3.Expr.expr list -> t -> Z3.Model.model -> Program_counter.t -> Gas_cost.t

val dec_push : Enc_consts.t -> Z3.Model.model -> Program_counter.t -> Instruction.t -> Instruction.t

val dec_instr : Enc_consts.t -> Z3.Model.model -> Program_counter.t -> Instruction.t
