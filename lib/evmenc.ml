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
}

let mk_state = {
  stack = Z3.FuncDecl.mk_func_decl_s (!ctxt) "stack"
      (* stack (j, n) = nth stack element after j instructions *)
      [int_sort; bv_sort sas]
      (bv_sort ses)
}

(* INIT: init stack with all 0 *)
let init st =
  let open Z3Ops in
  (* encode stack address size *)
  let n = bvconst "n" sas in
  (* encode 0 *)
  let z = bvnum 0 ses in
  forall n (st.stack @@ [num 0; n] == z)


let enc_opcode b = match b with
  | ADD -> failwith "smt library access"
  | _   -> failwith "other opcodes"


let super_optimize _ = failwith "not implemented"
