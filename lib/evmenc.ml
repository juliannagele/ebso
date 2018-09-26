open Core
open Z3util

(* stack address size; design decision/quick fix: the slot 2^sas - 1 is reserved
   for exception handling, otherwise the stack counter wraps around
   --> max stack size 2^sas - 1 *)
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
  exc_halt : Z3.FuncDecl.func_decl;
}

let mk_state = {
  (* stack(j, n) = nth stack element after j instructions *)
  stack = func_decl "stack" [int_sort; bv_sort sas] (bv_sort ses);
  (* sc(j) = index of the next free slot on the stack after j instructions *)
  stack_ctr = func_decl "sc" [int_sort] (bv_sort sas);
  (* exc_halt(j) is true if exceptional halting occurs after j instructions *)
  exc_halt = func_decl "exc_halt" [int_sort] bool_sort;
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
  && (st.exc_halt @@ [num 0] == btm)

(* TODO: check data layout on stack *)
let enc_stackarg x = bvnum x ses

let enc_push x st j =
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
  forall n ((n < sc) ==> (sk' n == sk n)) &&
  (* check for stack overflow *)
  (st.exc_halt @@ [j + one] == ~! (nuw sc (bvnum 1 sas) `Add))

let enc_binop op st j =
  let open Z3Ops in
  let n = bvconst "n" sas in
  let sk n = st.stack @@ [j; n] and sk' n = st.stack @@ [j + one; n] in
  let sc = st.stack_ctr @@ [j] and sc'= st.stack_ctr @@ [j + one] in
  (* two elements are consumed, one is added *)
  (sc' == (sc - bvnum 1 sas)) &&
  (* the new top element is the result of applying op to the previous two *)
  (sk' (sc - bvnum 2 sas) == op (sk (sc - bvnum 2 sas)) (sk (sc - bvnum 1 sas))) &&
  (* all elements below remain unchanged *)
  forall n ((n < (sc - bvnum 2 sas)) ==> (sk' n == sk n)) &&
  (* check for stack underflow *)
  (st.exc_halt @@ [j + one] == ((sc' - (bvnum 2 sas)) < (bvnum 0 sas)))

let enc_add = enc_binop (<+>)
(* effect of instruction on state st after j steps *)
let enc_opcode st j = function
  | PUSH x -> enc_push x st j
  | ADD -> failwith "smt library access"
  | _   -> failwith "other opcodes"


let super_optimize _ = failwith "not implemented"
