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
open Program
open Enc_consts

module PC = Program_counter
module GC = Gas_cost
module SI = Stack_index

(* TODO move uso *)
let enc_search_space ea st =
  let open Z3Ops in
  let j = PC.const "j" in
  let enc_cis =
    List.map ea.cis ~f:(fun is ->
        (ea.fis @@ [j] == Opcode.enc (Opcode.from_instr ea.opcodes is))
           ==> (Evm_state.enc_instruction ea st j is))
  in
  (* optimization potential:
     choose opcodes = 1 .. |cis| and demand fis (j) < |cis| *)
  let in_cis =
    List.map ea.cis ~f:(fun is -> ea.fis @@ [j] == Opcode.enc (Opcode.from_instr ea.opcodes is))
  in
  forall j (((j < ea.kt) && (j >= PC.init)) ==> conj enc_cis && disj in_cis) &&
  ea.kt >= PC.init

(* TODO move uso *)
let enc_super_opt ea =
  let open Z3Ops in
  let sts = Evm_state.mk ea "_s" in
  let stt = Evm_state.mk ea "_t" in
  let ks = PC.enc (Program.length ea.p) in
  foralls (forall_vars ea)
    (Evm_state.enc_program ea sts &&
     enc_search_space ea stt &&
     Evm_state.enc_equiv ea sts stt &&
     Used_gas.enc_used_more sts.used_gas ks stt.used_gas ea.kt &&
     (* bound the number of instructions in the target; aids solver in showing
        unsat, i.e., that program is optimal *)
     ea.kt <= PC.enc (PC.of_int (GC.to_int (total_gas_cost ea.p))))

(* TODO move transl_val *)
let enc_trans_val ea tp =
  let open Z3Ops in
  let sts = Evm_state.mk ea "_s" in
  let stt = Evm_state.mk ea "_t" in
  let kt = PC.enc (Program.length tp) and ks = PC.enc (Program.length ea.p) in
  (* we're asking for inputs that distinguish the programs *)
  existss (ea.xs @ List.concat (Map.data ea.uis))
    (* encode source and target program *)
    ((List.foldi tp ~init:(Evm_state.enc_program ea sts)
        ~f:(fun j enc oc -> enc <&> Evm_state.enc_instruction ea stt (PC.enc (PC.of_int j)) oc)) &&
     (* they start in the same state *)
     (Evm_state.enc_equiv_at sts stt PC.init PC.init) &&
     (Used_gas.enc_equvivalence_at sts.used_gas stt.used_gas PC.init) &&
     (* but their final state is different *)
     ~! (Evm_state.enc_equiv_at sts stt ks kt))

(* TODO move bso *)
(* classic superoptimzation: generate & test *)
let enc_classic_so_test ea cp js =
  let open Z3Ops in
  let sts = Evm_state.mk ea "_s" in
  let stc = Evm_state.mk ea "_c" in
  let kt = PC.enc (Program.length cp) and ks = PC.enc (Program.length ea.p) in
  foralls (forall_vars ea)
    (* encode source program*)
    ((Evm_state.enc_program ea sts) &&
     (* all instructions from candidate program are used in some order *)
     distinct js &&
     (conj (List.map js ~f:(fun j -> (j < kt) && (j >= PC.init)))) &&
     (* encode instructions from candidate program *)
     conj (List.map2_exn cp js ~f:(fun i j -> Evm_state.enc_instruction ea stc j i)) &&
     (* they start in the same state *)
     (Evm_state.enc_equiv_at sts stc PC.init PC.init) &&
     (Used_gas.enc_equvivalence_at sts.used_gas stc.used_gas PC.init) &&
     (* and their final state is the same *)
     (Evm_state.enc_equiv_at sts stc ks kt))

let dec_super_opt ea m =
  let k = PC.dec @@ eval_const m ea.kt in
  Program.init k ~f:(Evm_state.dec_instr ea m)

let dec_classic_super_opt ea m cp js =
  let js = List.map js ~f:(fun j -> eval_const m j |> PC.dec) in
  List.sort ~compare:(fun (_, j1) (_, j2) -> PC.compare j1 j2) (List.zip_exn cp js)
  |> List.mapi ~f:(fun j (i, _) -> Evm_state.dec_push ea m (PC.of_int j) i)
