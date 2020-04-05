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
  exc_halt : Exc_halt.t;
  used_gas : Used_gas.t;
}

let mk ea idx =
  { stack = Evm_stack.mk ea idx;
    storage = Evm_storage.mk ea idx;
    (* exc_halt(j) is true if exceptional halting occurs after j instructions *)
    exc_halt = Exc_halt.mk ea idx;
    (* gas(j) = amount of gas used to execute the first j instructions *)
    used_gas = Used_gas.mk ea idx;
  }

let init (ea : Enc_consts.t) st =
  let open Z3Ops in
  (* careful: if stack_depth is larger than 2^sas, no checks *)
  Evm_stack.init st.stack (Program.stack_depth ea.p) ea.xs
  && Exc_halt.init st.exc_halt
  && Used_gas.init st.used_gas
  && Evm_storage.init st.storage st.stack (Program.poss_of_instr ea.p SLOAD @ Program.poss_of_instr ea.p SSTORE) ea.ss

let enc_equiv_at sts stt js jt =
  let open Z3Ops in
  Evm_stack.enc_equiv_at sts.stack stt.stack js jt &&
  Exc_halt.enc_equiv_at sts.exc_halt stt.exc_halt js jt &&
  Evm_storage.enc_equiv_at sts.storage stt.storage js jt

(* we only demand equivalence at kt *)
let enc_equiv (ea : Enc_consts.t) sts stt =
  let ks = PC.enc (Program.length ea.p) and kt = ea.kt in
  let open Z3Ops in
  (* intially source and target states equal *)
  enc_equiv_at sts stt PC.init PC.init &&
  (* initally source and target gas are equal *)
  (Used_gas.enc_equvivalence_at sts.used_gas stt.used_gas PC.init) &&
  (* after the programs have run source and target states equal *)
  enc_equiv_at sts stt ks kt

let eval_state_func_decl  m j ?(n = []) ?(xs = []) f =
  eval_func_decl m f (xs @ [PC.enc j] @ n)

let eval_stack ?(xs = []) st m i n =
  eval_state_func_decl m i ~n:[SI.enc n] ~xs:xs st.stack.decl

let eval_stack_ctr st m i = eval_state_func_decl m i st.stack.ctr_decl

let eval_storage ?(xs = []) st m j k =
  eval_state_func_decl m j ~n:[k] ~xs:xs st.storage.decl

let eval_exc_halt st m i = eval_state_func_decl m i st.exc_halt.decl

let eval_gas ?(xs = []) st m i =
  eval_state_func_decl ~xs:xs m i st.used_gas.decl |> GC.dec
