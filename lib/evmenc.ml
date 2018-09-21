open Core
open Z3util

(* stack address size => max stack size 2^sas *)
let sas = 4

(* stack element size *)
let ses = 8

type stackarg = int [@@deriving show, eq]

type opcode =
  | ADD
  | PUSH of stackarg
  | POP
  | SUB
[@@deriving show { with_path = false }]

type state = {
  stack : Z3.FuncDecl.func_decl;
  stack_ctr : Z3.FuncDecl.func_decl;
}

let mk_state = {
  (* stack(j, n) = nth stack element after j instructions *)
  stack = func_decl "stack" [int_sort; bv_sort sas] (bv_sort ses);
  (* sc(j) = the index of the top element of the stack after j instructions *)
  stack_ctr = func_decl "sc" [int_sort] (bv_sort sas)
}

(* INIT: init stack with all 0 *)
let init st =
  let open Z3Ops in
  (* encode stack address size *)
  let n = bvconst "n" sas in
  (* encode 0 *)
  let z = bvnum 0 ses in
  forall n (st.stack @@ [num 0; n] == z)
  (* set stack counter to 0 *)
  && (st.stack_ctr @@ [num 0] == bvnum 0 sas)


let enc_opcode b = match b with
  | ADD -> failwith "smt library access"
  | _   -> failwith "other opcodes"


let super_optimize _ = failwith "not implemented"
