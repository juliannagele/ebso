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
open Instruction.T

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

(* effect of instruction is on state st after j steps *)
let enc_instruction (ea : Enc_consts.t) st j is =
  let enc_effect =
    let open Evm_stack in
    let open Instruction in
    match is with
    | PUSH x -> enc_push ea.a st.stack j x
    | POP -> enc_pop st.stack j
    | ADD -> enc_binop st.stack j Word.enc_add
    | SUB -> enc_binop st.stack j Word.enc_sub
    | MUL -> enc_binop st.stack j Word.enc_mul
    | DIV -> enc_binop st.stack j Word.enc_div
    | SDIV -> enc_binop st.stack j Word.enc_sdiv
    | MOD -> enc_binop st.stack j Word.enc_mod
    | SMOD -> enc_binop st.stack j Word.enc_smod
    | ADDMOD -> enc_ternaryop st.stack j Word.enc_addmod
    | MULMOD -> enc_ternaryop st.stack j Word.enc_mulmod
    | LT -> enc_binop st.stack j Word.enc_lt
    | GT -> enc_binop st.stack  j Word.enc_gt
    | SLT -> enc_binop st.stack j Word.enc_slt
    | SGT -> enc_binop st.stack j Word.enc_sgt
    | EQ -> enc_binop st.stack j Word.enc_eq
    | ISZERO -> enc_unaryop st.stack j Word.enc_iszero
    | AND -> enc_binop st.stack j Word.enc_and
    | OR -> enc_binop st.stack j Word.enc_or
    | XOR -> enc_binop st.stack j Word.enc_xor
    | NOT -> enc_unaryop st.stack j Word.enc_not
    | SWAP idx -> enc_swap st.stack j (idx_to_enum idx)
    | DUP idx -> enc_dup st.stack j (idx_to_enum idx)
    | SLOAD -> Evm_storage.enc_sload st.storage st.stack j
    | SSTORE -> Evm_storage.enc_sstore st.storage st.stack j
    | _ when List.mem uninterpreted is ~equal:Instruction.equal ->
      Uninterpreted_instruction.enc ea st.stack j is
    | i -> failwith ("Encoding for " ^ [%show: Instruction.t] i ^ " not implemented.")
  in
  let open Z3Ops in
  let sc = st.stack.ctr j in
  let k = st.stack.el j (sc - SI.enc 1) in
  let v = st.storage.el j k in
  let v' = st.stack.el j (sc - SI.enc 2) in
  let enc_used_gas = Used_gas.enc v v' is st.used_gas j in
  let enc_stack_ctr = Evm_stack.enc_stack_ctr is st.stack j in
  let enc_exc_halt = Exc_halt.enc sc is st.exc_halt j in
  let enc_pres = Evm_stack.pres is st.stack j &&  Evm_storage.pres is st.storage j in
  enc_effect && enc_used_gas && enc_stack_ctr && enc_pres && enc_exc_halt

let enc_program (ea : Enc_consts.t) st =
  let open Z3Ops in
  List.foldi ~init:(init ea st && Uninterpreted_instruction.init ea st.stack)
    ~f:(fun j enc oc -> enc && enc_instruction ea st (PC.enc (PC.of_int j)) oc) ea.p

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

let eval_fis (ea : Enc_consts.t) m j = eval_state_func_decl m j ea.fis |> Opcode.dec

let eval_a (ea : Enc_consts.t) m j = eval_state_func_decl m j ea.a |> Z3.Arithmetic.Integer.numeral_to_string

let dec_push ea m j = function
  | PUSH Tmpl -> PUSH (Word (Word.from_string (eval_a ea m j)))
  | i -> i

let dec_instr ea m j =
  eval_fis ea m j |> Opcode.to_instr ea.opcodes |> dec_push ea m j
