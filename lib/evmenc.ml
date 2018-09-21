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
  (* sc(j) = index of the next free slot on the stack after j instructions *)
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

(* TODO: check data layout on stack *)
let enc_stackarg x = bvnum x ses

let enc_push x st j =
  (* TODO: check for stack_overflow *)
  let open Z3Ops in
  let n = bvconst "n" sas in
  (* the stack before and after the PUSH *)
  let sk n = st.stack @@ [j; n] and sk' n = st.stack @@ [j + one; n] in
  (* the stack counter before and after the PUSH *)
  let sc = st.stack_ctr @@ [j] and sc'= st.stack_ctr @@ [j + one] in
  (* there will be one more element on the stack after PUSHing *)
  (sc' == (sc + bvnum 1 sas)) &&
  (* that element will be x *)
  sk' sc == enc_stackarg x &&
  (* all old elements stay the same *)
  forall n ((n < sc) ==> (sk' n == sk n))

let enc_add _ _ = failwith "not implemented"

(* effect of instruction on state st after j steps *)
let enc_opcode st j = function
  | PUSH x -> enc_push x st j
  | ADD -> failwith "smt library access"
  | _   -> failwith "other opcodes"


let super_optimize _ = failwith "not implemented"
