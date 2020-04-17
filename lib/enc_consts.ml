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

type t = {
  p : Program.t;
  tp : Program.t option;
  cis : Instruction.t list;
  kt : Z3.Expr.expr;
  fis : Z3.FuncDecl.func_decl;
  a : Z3.FuncDecl.func_decl;
  cs : Z3.Expr.expr list;
  uis : Z3.Expr.expr list Instruction.Map.t;
  opcodes : Opcode.instr_map;
  xs : Z3.Expr.expr list;
  ss : Z3.Expr.expr list;
  roms : Z3.FuncDecl.func_decl Instruction.Map.t
}

let mk_unint_vars p =
  let module M = Instruction.Map in
  let add_xi i xs = xs @ [Word.const (Instruction.unint_name (List.length xs) i)]
  in List.fold p ~init:M.empty ~f:(fun ue i ->
      if Instruction.is_uninterpreted i
      then M.update ue i ~f:(function | Some xs -> if Instruction.is_const i then xs else add_xi i xs
                                      | None -> [Word.const (Instruction.unint_name 0 i)])
      else ue)

let mk_unint_roms p vc =
  let module M = Instruction.Map in
  List.fold p ~init:M.empty ~f:(fun ue i ->
      if Instruction.is_uninterpreted i && not (Instruction.is_const i)
      then M.update ue i ~f:(function | Some f -> f
                                      | None ->
                                        let arity = Instruction.arity i + vc in
                                        func_decl (Instruction.unint_rom_name i) (List.init arity ~f:(fun _ -> !Word.sort)) !Word.sort)
      else ue)

let mk_store_vars p = List.fold p ~init:[] ~f:(fun vs i ->
    if Instruction.equal SLOAD i || Instruction.equal SSTORE i
    then vs @ [Word.const (Instruction.unint_name (List.length vs) i)]
    else vs)

(* list of free variables x_0 .. x_(stack_depth -1) for words already on stack *)
(* careful: no check that this does not generate more than max stacksize variables *)
let mk_input_vars p =
  List.init (Program.stack_depth p) ~f:(fun i -> Word.const ("x_" ^ Int.to_string i))

(* arguments of PUSH which are too large to fit in word size *)
let mk_push_const_vars p = List.map (Program.consts p) ~f:(Word.const)

(* list of candidate instructions *)
let mk_cis p uis = function
  | `Progr -> Program.cis_of_progr p
  | `User cis -> List.stable_dedup cis
  | `All ->
    let const_pushs = List.map (Program.consts p) ~f:(fun c -> PUSH (Word (Const c))) in
    Instruction.encodable @ const_pushs @ uis

let mk p ?(tp=None) cis_mde =
  let tpl = Option.value ~default:[] tp in
  let uis =
    Instruction.Map.merge ~f:(fun ~key:_ -> function
          `Left uis -> Some uis
        | `Right uis -> Some uis
        | `Both (uis1, uis2) -> Some (List.stable_dedup (uis1 @ uis2)))
      (mk_unint_vars p) (mk_unint_vars tpl)
  in
  let cis = mk_cis p (Instruction.Map.keys uis) cis_mde in
  let xs = mk_input_vars p in
  let cs = mk_push_const_vars (p @ tpl) in
  let ss = List.stable_dedup (mk_store_vars p @ mk_store_vars tpl) in
{ (* source program *)
  p = p;
  (* optional target program -- set when using translation validation *)
  tp = tp;
  (* candidate instruction set: instructions to choose from in target program *)
  cis = cis;
  (* number of instructions in target program *)
  kt = PC.const "k";
  (* target program *)
  fis = func_decl "instr" [PC.sort] Opcode.sort;
  (* arguments for PUSH instrucions in target program *)
  a = func_decl "a" [PC.sort] !Word.sort;
  cs = cs;
  uis = uis;
  opcodes = Opcode.mk_instr_map cis;
  xs = xs;
  (* intial words in storage *)
  ss = ss;
  (* read only memories for uninterpreted instructions: return a word
     depending on given arguments, i.e., the arguments of the
     instruction in the program, _and_ depending on the forall
     quantified variables, source and target program use the same
     roms, hence roms cannot be in state without adapting equvivalence
     *)
  roms = mk_unint_roms (p @ tpl)
      (List.length (xs @ ss @ cs @ List.concat (Instruction.Map.data uis)));
}

let mk_trans_val p tp = mk p ~tp:(Some tp)

(* project all forall quantified variables *)
let forall_vars ea = ea.xs @ ea.ss @ ea.cs @ List.concat (Instruction.Map.data ea.uis)
