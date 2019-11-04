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
  storage : Evm_storage.t;
  exc_halt : Z3.FuncDecl.func_decl;
  used_gas : Used_gas.t;
}

let mk ea idx =
  { stack = Evm_stack.mk ea idx;
    storage = Evm_storage.mk ea idx;
    (* exc_halt(j) is true if exceptional halting occurs after j instructions *)
    exc_halt = func_decl ("exc_halt" ^ idx) [PC.sort] bool_sort;
    (* gas(j) = amount of gas used to execute the first j instructions *)
    used_gas = Used_gas.mk ea idx;
  }

let eval_state_func_decl  m j ?(n = []) ?(xs = []) f =
  eval_func_decl m f (xs @ [PC.enc j] @ n)

let eval_stack ?(xs = []) st m i n =
  eval_state_func_decl m i ~n:[SI.enc n] ~xs:xs st.stack.decl

let eval_stack_ctr st m i = eval_state_func_decl m i st.stack.ctr

let eval_storage ?(xs = []) st m j k =
  eval_state_func_decl m j ~n:[k] ~xs:xs st.storage.decl

let eval_exc_halt st m i = eval_state_func_decl m i st.exc_halt

let eval_gas ?(xs = []) st m i =
  eval_state_func_decl ~xs:xs m i st.used_gas.decl |> GC.dec
