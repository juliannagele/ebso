(*   Copyright 2018 Julian Nagele and Maria A Schett

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
open Instruction
open Program
open Enc_consts
open Evm_state

module PC = Program_counter
module GC = Gas_cost
module SI = Stack_index

let init ea st =
  let open Z3Ops in
  (* careful: if stack_depth is larger than 2^sas, no checks *)
  Evm_stack.init st.stack (stack_depth ea.p) ea.xs
  && (st.exc_halt @@ [PC.init] == btm)
  && Used_gas.init st.used_gas
  && Evm_storage.init st.storage st.stack (poss_of_instr ea.p SLOAD @ poss_of_instr ea.p SSTORE) ea.ss
  && Map.fold ea.roms ~init:top ~f:(fun ~key:i ~data:f e -> e && Uninterpreted_instruction.init_rom ea st i f)

(* effect of instruction on state st after j steps *)
let enc_instruction ea st j is =
  let enc_effect =
    let open Evm_stack in
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
      Uninterpreted_instruction.enc ea st j is
    | i -> failwith ("Encoding for " ^ [%show: Instruction.t] i ^ " not implemented.")
  in
  let (d, a) = delta_alpha is in let diff = (a - d) in
  let open Z3Ops in
  let sc = st.stack.ctr @@ [j] in
  let k = st.stack.el j (sc - SI.enc 1) in
  let v = st.storage.el j k in
  let v' = st.stack.el j (sc - SI.enc 2) in
  let enc_used_gas = Used_gas.enc v v' is st.used_gas j in
  let enc_stack_ctr = st.stack.ctr @@ [j + one] == (sc + SI.enc diff)
  in
  let enc_exc_halt =
    let underflow = if Int.is_positive d then (sc - (SI.enc d)) < (SI.enc 0) else btm in
    let overflow =
      if Int.is_positive diff then
        match Z3.Sort.get_sort_kind !SI.sort with
        | BV_SORT -> ~! (nuw sc (SI.enc diff) `Add)
        | INT_SORT -> (sc + (SI.enc diff)) > (SI.enc 1024)
        | _ -> btm
      else btm
    in
    st.exc_halt @@ [j + one] == (st.exc_halt @@ [j] || underflow || overflow)
  in
  let enc_pres = Evm_stack.pres is st.stack j &&  Evm_storage.pres is st.storage j in
  enc_effect && enc_used_gas && enc_stack_ctr && enc_pres && enc_exc_halt

let enc_search_space ea st =
  let open Z3Ops in
  let j = PC.const "j" in
  let enc_cis =
    List.map ea.cis ~f:(fun is ->
        (ea.fis @@ [j] == Opcode.enc (Opcode.from_instr ea.opcodes is)) ==> (enc_instruction ea st j is))
  in
  (* optimization potential:
     choose opcodes = 1 .. |cis| and demand fis (j) < |cis| *)
  let in_cis =
    List.map ea.cis ~f:(fun is -> ea.fis @@ [j] == Opcode.enc (Opcode.from_instr ea.opcodes is))
  in
  forall j (((j < ea.kt) && (j >= PC.init)) ==> conj enc_cis && disj in_cis) &&
  ea.kt >= PC.init

let enc_equivalence_at sts stt js jt =
  let open Z3Ops in
  Evm_stack.enc_equiv_at sts.stack stt.stack js jt &&
  (* source and target exceptional halting are equal *)
  sts.exc_halt @@ [js] == stt.exc_halt @@ [jt] &&
  Evm_storage.enc_equiv_at sts.storage stt.storage js jt

(* we only demand equivalence at kt *)
let enc_equivalence ea sts stt =
  let ks = PC.enc (Program.length ea.p) and kt = ea.kt in
  let open Z3Ops in
  (* intially source and target states equal *)
  enc_equivalence_at sts stt PC.init PC.init &&
  (* initally source and target gas are equal *)
  (Used_gas.enc_equvivalence_at sts.used_gas stt.used_gas PC.init) &&
  (* after the programs have run source and target states equal *)
  enc_equivalence_at sts stt ks kt

let enc_program ea st =
  List.foldi ~init:(init ea st)
    ~f:(fun j enc oc -> enc <&> enc_instruction ea st (PC.enc (PC.of_int j)) oc) ea.p

let enc_super_opt ea =
  let open Z3Ops in
  let sts = Evm_state.mk ea "_s" in
  let stt = Evm_state.mk ea "_t" in
  let ks = PC.enc (Program.length ea.p) in
  foralls (forall_vars ea)
    (enc_program ea sts &&
     enc_search_space ea stt &&
     enc_equivalence ea sts stt &&
     Used_gas.enc_used_more sts.used_gas ks stt.used_gas ea.kt &&
     (* bound the number of instructions in the target; aids solver in showing
        unsat, i.e., that program is optimal *)
     ea.kt <= PC.enc (PC.of_int (GC.to_int (total_gas_cost ea.p))))

let enc_trans_val ea tp =
  let open Z3Ops in
  let sts = Evm_state.mk ea "_s" in
  let stt = Evm_state.mk ea "_t" in
  let kt = PC.enc (Program.length tp) and ks = PC.enc (Program.length ea.p) in
  (* we're asking for inputs that distinguish the programs *)
  existss (ea.xs @ List.concat (Map.data ea.uis))
    (* encode source and target program *)
    ((List.foldi tp ~init:(enc_program ea sts)
        ~f:(fun j enc oc -> enc <&> enc_instruction ea stt (PC.enc (PC.of_int j)) oc)) &&
     (* they start in the same state *)
     (enc_equivalence_at sts stt PC.init PC.init) &&
     (Used_gas.enc_equvivalence_at sts.used_gas stt.used_gas PC.init) &&
     (* but their final state is different *)
     ~! (enc_equivalence_at sts stt ks kt))

(* classic superoptimzation: generate & test *)
let enc_classic_so_test ea cp js =
  let open Z3Ops in
  let sts = Evm_state.mk ea "_s" in
  let stc = Evm_state.mk ea "_c" in
  let kt = PC.enc (Program.length cp) and ks = PC.enc (Program.length ea.p) in
  foralls (forall_vars ea)
    (* encode source program*)
    ((enc_program ea sts) &&
     (* all instructions from candidate program are used in some order *)
     distinct js &&
     (conj (List.map js ~f:(fun j -> (j < kt) && (j >= PC.init)))) &&
     (* encode instructions from candidate program *)
     conj (List.map2_exn cp js ~f:(fun i j -> enc_instruction ea stc j i)) &&
     (* they start in the same state *)
     (enc_equivalence_at sts stc PC.init PC.init) &&
     (Used_gas.enc_equvivalence_at sts.used_gas stc.used_gas PC.init) &&
     (* and their final state is the same *)
     (enc_equivalence_at sts stc ks kt))


let eval_fis ea m j = eval_state_func_decl m j ea.fis |> Opcode.dec

let eval_a ea m j = eval_state_func_decl m j ea.a |> Z3.Arithmetic.Integer.numeral_to_string

let dec_push ea m j = function
  | PUSH Tmpl -> PUSH (Word (Word.from_string (eval_a ea m j)))
  | i -> i

let dec_instr ea m j =
  eval_fis ea m j |> Opcode.to_instr ea.opcodes |> dec_push ea m j

let dec_super_opt ea m =
  let k = PC.dec @@ eval_const m ea.kt in
  Program.init k ~f:(dec_instr ea m)

let dec_classic_super_opt ea m cp js =
  let js = List.map js ~f:(fun j -> eval_const m j |> PC.dec) in
  List.sort ~compare:(fun (_, j1) (_, j2) -> PC.compare j1 j2) (List.zip_exn cp js)
  |> List.mapi ~f:(fun j (i, _) -> dec_push ea m (PC.of_int j) i)
