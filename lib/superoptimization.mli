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
module Uso : sig
  val enc_search_space : Enc_consts.t -> Evm_state.t -> Z3.Expr.expr
  val enc : Enc_consts.t -> Z3.Expr.expr
  val dec : Enc_consts.t -> Z3.Model.model -> Program.t
end

module Bso : sig
  val enc : Enc_consts.t -> Program.t -> Z3.Expr.expr list -> Z3.Expr.expr
  val dec : Enc_consts.t -> Z3.Model.model -> Program.t -> Z3.Expr.expr list -> Program.t
end

val enc_trans_val : Enc_consts.t -> Z3.Expr.expr
