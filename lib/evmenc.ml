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

(* get the top d elements of the stack *)
let enc_top_d_of_sk ea st j d =
  let open Z3Ops in
  let pos l = (st.stack_ctr @@ [j]) - SI.enc (Int.succ l) in
  List.init d ~f:(fun l -> st.stack @@ (forall_vars ea @ [j; pos l]))

let init_rom ea st i rom =
  let open Z3Ops in
  let d = arity i in
  let js = poss_of_instr ea.p i in
  let us = Map.find_exn ea.uis i in
  let ajs = List.map js ~f:(fun j -> enc_top_d_of_sk ea st (PC.enc j) d) in
  let w_dflt = Word.enc_int 0 in
  let ws = List.init d ~f:(fun l -> Word.const ("w" ^ [%show: int] l)) in
  foralls ws (
    (rom @@ (forall_vars ea @ ws)) ==
      List.fold_right (List.zip_exn ajs us) ~init:w_dflt
        ~f:(fun (aj, uj) enc -> ite (conj (List.map2_exn aj ws ~f:(==))) uj enc)
  )

let init_storage ea st =
  let open Z3Ops in
  let js = poss_of_instr ea.p SLOAD @ poss_of_instr ea.p SSTORE in
  let ks = List.concat_map js ~f:(fun j -> enc_top_d_of_sk ea st (PC.enc j) 1) in
  let w_dflt = Word.enc_int 0 in
  let w = Word.const "w" in
  forall w (
    (st.storage @@ (forall_vars ea @ [PC.init; w]) ==
     List.fold_right (List.zip_exn ks ea.ss) ~init:w_dflt
       ~f:(fun (k, s) enc -> ite (w == k) s enc)))

let init ea st =
  let open Z3Ops in
  (* careful: if stack_depth is larger than 2^sas, no checks *)
  let skd = stack_depth (ea.p) in
  (* set stack counter to skd *)
  (st.stack_ctr @@ [PC.init] == SI.enc skd)
  (* set inital words on stack *)
  && conj (List.mapi ea.xs ~f:(fun i x ->
      st.stack @@ (forall_vars ea @ [PC.init; SI.enc i]) == x))
  && (st.exc_halt @@ [PC.init] == btm)
  && (st.used_gas @@ (forall_vars ea @ [PC.init]) == GC.enc GC.zero)
  && init_storage ea st
  && Map.fold ea.roms ~init:top ~f:(fun ~key:i ~data:f e -> e && init_rom ea st i f)

let enc_push ea st j x =
  let open Z3Ops in
  (* the stack after the PUSH *)
  let sk' n = st.stack @@ (forall_vars ea @ [j + one; n]) in
  (* the stack counter before the PUSH *)
  let sc = st.stack_ctr @@ [j] in
  (* the new top word will be x *)
  sk' sc == Pusharg.enc ea.a j x

(* the only effect of POP is to change the stack counter *)
let enc_pop _ _ _ = top

let enc_unaryop ea st j op =
  let open Z3Ops in
  let sk n = st.stack @@ (forall_vars ea @ [j; n])
  and sk' n = st.stack @@ (forall_vars ea @ [j + one; n]) in
  let sc = st.stack_ctr @@ [j] and sc'= st.stack_ctr @@ [j + one] in
  (sk' (sc' - SI.enc 1) == op (sk (sc - SI.enc 1)))

let enc_binop ea st j op =
  let open Z3Ops in
  let sk n = st.stack @@ (forall_vars ea @ [j; n])
  and sk' n = st.stack @@ (forall_vars ea @ [j + one; n]) in
  let sc = st.stack_ctr @@ [j] and sc'= st.stack_ctr @@ [j + one] in
  (* the new top word is the result of applying op to the previous two *)
  (sk' (sc' - SI.enc 1) == op (sk (sc - SI.enc 1)) (sk (sc - SI.enc 2)))

let enc_ternaryop ea st j op =
  let open Z3Ops in
  let sk n = st.stack @@ (forall_vars ea @ [j; n])
  and sk' n = st.stack @@ (forall_vars ea @ [j + one; n]) in
  let sc = st.stack_ctr @@ [j] and sc'= st.stack_ctr @@ [j + one] in
  let w3 = sk (sc - SI.enc 3) and w2 = sk (sc - SI.enc 2) and w1 = sk (sc - SI.enc 1) in
  sk' (sc' - SI.enc 1) == op w1 w2 w3

let enc_swap ea st j idx =
  let sc_idx = SI.enc (idx + 1) in
  let open Z3Ops in
  let sk n = st.stack @@ (forall_vars ea @ [j; n])
  and sk' n = st.stack @@ (forall_vars ea @ [j + one; n]) in
  let sc = st.stack_ctr @@ [j] and sc'= st.stack_ctr @@ [j + one] in
  (* the new top word is the 1+idx'th from the old stack *)
  (sk' (sc' - SI.enc 1) == sk (sc - sc_idx)) &&
  (* the new 1+idx'th word is the top from the old stack*)
  (sk' (sc' - sc_idx) == sk (sc - SI.enc 1)) &&
  (* the words between top and idx+1 are not touched *)
  conj (List.init (Int.pred idx) ~f:(fun i ->
      let sc_iidx = SI.enc (Int.(-) idx i) in
      (sk' (sc' - sc_iidx) == sk (sc - sc_iidx))))

let enc_dup ea st j idx =
  let sc_idx = SI.enc idx in
  let open Z3Ops in
  let sk n = st.stack @@ (forall_vars ea @ [j; n])
  and sk' n = st.stack @@ (forall_vars ea @ [j + one; n]) in
  let sc = st.stack_ctr @@ [j] and sc'= st.stack_ctr @@ [j + one] in
  (* the new top word is the idx'th from the old stack *)
  (sk' (sc' - SI.enc 1) == sk (sc - sc_idx)) &&
  (* all words down to idx are not touched *)
  conj (List.init idx ~f:(fun i ->
      let sc_iidx = SI.enc (Int.(-) idx i) in
      (sk' (sc - sc_iidx) == sk (sc - sc_iidx))))

let enc_const_uninterpreted ea st j i =
  let name = Instruction.unint_name 0 i in
  enc_push ea st j (Pusharg.Word (Const name))

let enc_nonconst_uninterpreted ea st j i =
  let rom = Map.find_exn ea.roms i in
  let open Z3Ops in
  let sk' n = st.stack @@ (forall_vars ea @ [j + one; n])
  and sc'= st.stack_ctr @@ [j + one] in
  let ajs = enc_top_d_of_sk ea st j (arity i) in
  (sk' (sc' - SI.enc 1)) == (rom @@ ((forall_vars ea) @ ajs))

let enc_sload ea st j =
  let open Z3Ops in
  let sk n = st.stack @@ (forall_vars ea @ [j; n])
  and sk' n = st.stack @@ (forall_vars ea @ [j + one; n]) in
  let sc = st.stack_ctr @@ [j] and sc'= st.stack_ctr @@ [j + one] in
  (sk' (sc' - SI.enc 1)) ==
  (st.storage @@ ((forall_vars ea) @ [j; sk (sc - SI.enc 1)]))

let enc_sstore ea st j =
  let open Z3Ops in
  let sk n = st.stack @@ (forall_vars ea @ [j; n]) and sc = st.stack_ctr @@ [j] in
  let strg w = st.storage @@ (forall_vars ea @ [j; w]) in
  let strg' w = st.storage @@ (forall_vars ea @ [j + one; w]) in
  let w = Word.const "w" in
  forall w (strg' w == (ite (w == sk (sc - SI.enc 1)) (sk (sc - SI.enc 2)) (strg w)))

(* effect of instruction on state st after j steps *)
let enc_instruction ea st j is =
  let enc_effect =
    match is with
    | PUSH x -> enc_push ea st j x
    | POP -> enc_pop ea st j
    | ADD -> enc_binop ea st j Word.enc_add
    | SUB -> enc_binop ea st j Word.enc_sub
    | MUL -> enc_binop ea st j Word.enc_mul
    | DIV -> enc_binop ea st j Word.enc_div
    | SDIV -> enc_binop ea st j Word.enc_sdiv
    | MOD -> enc_binop ea st j Word.enc_mod
    | SMOD -> enc_binop ea st j Word.enc_smod
    | ADDMOD -> enc_ternaryop ea st j Word.enc_addmod
    | MULMOD -> enc_ternaryop ea st j Word.enc_mulmod
    | LT -> enc_binop ea st j Word.enc_lt
    | GT -> enc_binop ea st  j Word.enc_gt
    | SLT -> enc_binop ea st j Word.enc_slt
    | SGT -> enc_binop ea st j Word.enc_sgt
    | EQ -> enc_binop ea st j Word.enc_eq
    | ISZERO -> enc_unaryop ea st j Word.enc_iszero
    | AND -> enc_binop ea st j Word.enc_and
    | OR -> enc_binop ea st j Word.enc_or
    | XOR -> enc_binop ea st j Word.enc_xor
    | NOT -> enc_unaryop ea st j Word.enc_not
    | SWAP idx -> enc_swap ea st j (idx_to_enum idx)
    | DUP idx -> enc_dup ea st j (idx_to_enum idx)
    | SLOAD -> enc_sload ea st j
    | SSTORE -> enc_sstore ea st j
    | _ when List.mem uninterpreted is ~equal:Instruction.equal ->
      if is_const is then enc_const_uninterpreted ea st j is
      else enc_nonconst_uninterpreted ea st j is
    | i -> failwith ("Encoding for " ^ [%show: Instruction.t] i ^ " not implemented.")
  in
  let (d, a) = delta_alpha is in let diff = (a - d) in
  let open Z3Ops in
  let sc = st.stack_ctr @@ [j] in
  let sk n = st.stack @@ (forall_vars ea @ [j; n])
  and sk' n = st.stack @@ (forall_vars ea @ [j + one; n]) in
  let strg w = st.storage @@ (forall_vars ea @ [j; w])
  and strg' w = st.storage @@ (forall_vars ea @ [j + one; w]) in
  let ug = st.used_gas @@ (forall_vars ea @ [j])
  and ug' = st.used_gas @@ (forall_vars ea @ [j + one]) in
  let enc_used_gas =
    let cost =
      let k = sk (sc - SI.enc 1) in
      let v' = sk (sc - SI.enc 2) in
      let refund = GC.enc (GC.of_int 15000)
      and set = GC.enc (GC.of_int 20000)
      and reset = GC.enc (GC.of_int 5000) in
      match is with
      | SSTORE ->
        ite (strg k == Word.enc_int 0)
          (ite (v' == Word.enc_int 0) reset set)
          (ite (v' == Word.enc_int 0) (reset - refund) reset)
      | _ -> GC.enc (gas_cost is)
    in
    ug' == (ug + cost)
  in
  let enc_stack_ctr =
    st.stack_ctr @@ [j + one] == (sc + SI.enc diff)
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
  let enc_pres =
    let pres_storage = match is with
      | SSTORE -> top
      | _ ->
        let w = Word.const "w" in
        forall w (strg' w == strg w)
    in
    let n = SI.const "n" in
    (* all words below d stay the same *)
    (forall n ((n < sc - SI.enc d) ==> (sk' n == sk n))) && pres_storage
  in
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

let enc_equivalence_at ea sts stt js jt =
  let open Z3Ops in
  let n = SI.const "n" in
  let w = Word.const "w" in
  (* source and target stack counter are equal *)
  sts.stack_ctr @@ [js] == stt.stack_ctr @@ [jt] &&
  (* source and target exceptional halting are equal *)
  sts.exc_halt @@ [js] == stt.exc_halt @@ [jt] &&
  (* source and target stack are equal below the stack counter;
     note that it doesn't matter which stack counter is used, they are equal *)
  (forall n ((n < stt.stack_ctr @@ [jt]) ==>
             ((sts.stack @@ (forall_vars ea @ [js; n]))
              == (stt.stack @@ (forall_vars ea @ [jt; n]))))) &&
  (* source and target storage are equal *)
  (forall w ((sts.storage @@ (forall_vars ea @ [js; w]))
              == (stt.storage @@ (forall_vars ea @ [jt; w]))))

(* we only demand equivalence at kt *)
let enc_equivalence ea sts stt =
  let ks = PC.enc (Program.length ea.p) and kt = ea.kt in
  let open Z3Ops in
  (* intially source and target states equal *)
  enc_equivalence_at ea sts stt PC.init PC.init &&
  (* initally source and target gas are equal *)
  sts.used_gas @@ (forall_vars ea @ [PC.init]) ==
  stt.used_gas @@ (forall_vars ea @ [PC.init]) &&
  (* after the programs have run source and target states equal *)
  enc_equivalence_at ea sts stt ks kt

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
     sts.used_gas @@ (forall_vars ea @ [ks]) >
     stt.used_gas @@ (forall_vars ea @ [ea.kt]) &&
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
     (enc_equivalence_at ea sts stt PC.init PC.init) &&
     sts.used_gas @@ (forall_vars ea @ [PC.init]) ==
     stt.used_gas @@ (forall_vars ea @ [PC.init]) &&
     (* but their final state is different *)
     ~! (enc_equivalence_at ea sts stt ks kt))

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
     (enc_equivalence_at ea sts stc PC.init PC.init) &&
     sts.used_gas @@ (forall_vars ea @ [PC.init]) ==
     stc.used_gas @@ (forall_vars ea @ [PC.init]) &&
     (* and their final state is the same *)
     (enc_equivalence_at ea sts stc ks kt))

let eval_state_func_decl  m j ?(n = []) ?(xs = []) f =
  eval_func_decl m f (xs @ [PC.enc j] @ n)

let eval_stack ?(xs = []) st m i n =
  eval_state_func_decl m i ~n:[SI.enc n] ~xs:xs st.stack

let eval_stack_ctr st m i = eval_state_func_decl m i st.stack_ctr

let eval_storage ?(xs = []) st m j k =
  eval_state_func_decl m j ~n:[k] ~xs:xs st.storage

let eval_exc_halt st m i = eval_state_func_decl m i st.exc_halt

let eval_gas ?(xs = []) st m i =
  eval_state_func_decl ~xs:xs m i st.used_gas |> GC.dec

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
