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

module PC = Program_counter
module GC = Gas_cost
module SI = Stack_index

type t = {
  stack : Evm_stack.t;
  storage : Z3.FuncDecl.func_decl;
  exc_halt : Z3.FuncDecl.func_decl;
  used_gas : Z3.FuncDecl.func_decl;
}

let mk ea idx =
  let mk_vars_sorts vs = List.map vs ~f:(fun _ -> !Word.sort) in
  let vars_sorts = mk_vars_sorts (Enc_consts.forall_vars ea) in
  { stack = Evm_stack.mk ea idx;
    (* storage(_, j, k) = v if storage after j instructions contains word v for key k *)
    storage = func_decl ("storage" ^ idx) (vars_sorts @ [PC.sort; !Word.sort]) !Word.sort;
    (* exc_halt(j) is true if exceptional halting occurs after j instructions *)
    exc_halt = func_decl ("exc_halt" ^ idx) [PC.sort] bool_sort;
    (* gas(j) = amount of gas used to execute the first j instructions *)
    used_gas = func_decl ("used_gas" ^ idx) (vars_sorts @ [PC.sort]) GC.sort;
  }
