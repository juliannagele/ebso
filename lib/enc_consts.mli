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
  p : Program.t;
  cis : Instruction.t list;
  kt : Z3.Expr.expr;
  fis : Z3.FuncDecl.func_decl;
  a : Z3.FuncDecl.func_decl;
  cs : Z3.Expr.expr list;
  uis : Z3.Expr.expr list Instruction.Map.t;
  opcodes : Opcode.instr_map;
  xs : Z3.Expr.expr list;
  ss : Z3.Expr.expr list;
  roms : Z3.FuncDecl.func_decl Instruction.Map.t;
}

val mk :
    Instruction.t list ->
    [< `All | `Progr | `User of Instruction.t list ] -> t

val forall_vars : t -> Z3.Expr.expr list
