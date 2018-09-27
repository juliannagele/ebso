open Core
open Z3util

(* stack address size; design decision/quick fix: the slot 2^sas - 1 is reserved
   for exception handling, otherwise the stack counter wraps around
   --> max stack size 2^sas - 1 *)
let sas = 4

(* stack element size *)
let ses = 8

type stackarg = int [@@deriving show, eq]

type instr =
  | ADD
  | PUSH of stackarg
  | POP
  | SUB
[@@deriving show { with_path = false }]

type progr = instr list

let gas_cost = function
  | ADD -> 3
  | PUSH _ -> 2
  | POP -> 2
  | SUB -> 3

let total_gas_cost = List.fold ~init:0 ~f:(fun gc i -> gc + gas_cost i)

type state = {
  stack : Z3.FuncDecl.func_decl;
  stack_ctr : Z3.FuncDecl.func_decl;
  exc_halt : Z3.FuncDecl.func_decl;
  used_gas : Z3.FuncDecl.func_decl;
}

let mk_state = {
  (* stack(j, n) = nth stack element after j instructions *)
  stack = func_decl "stack" [int_sort; bv_sort sas] (bv_sort ses);
  (* sc(j) = index of the next free slot on the stack after j instructions *)
  stack_ctr = func_decl "sc" [int_sort] (bv_sort sas);
  (* exc_halt(j) is true if exceptional halting occurs after j instructions *)
  exc_halt = func_decl "exc_halt" [int_sort] bool_sort;
  (* gas(j) = amount of gas used to execute the first j instructions *)
  used_gas = func_decl "used_gas" [int_sort] int_sort;
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
  && (st.used_gas @@ [num 0] == num 0)

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
  (* check for exceptional halting  *)
  (st.exc_halt @@ [j + one] ==
  (* stack overflow occured or exceptional halting occured eariler *)
  (~! (nuw sc (bvnum 1 sas) `Add) || st.exc_halt @@ [j]))

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
  (* check for exceptional halting *)
  (st.exc_halt @@ [j + one] ==
  (* stack underflow occured or exceptional halting occured eariler *)
  ((sc' - (bvnum 2 sas)) < (bvnum 0 sas)) || st.exc_halt @@ [j])

let enc_add = enc_binop (<+>)
let enc_sub = enc_binop (<->)

(* effect of instruction on state st after j steps *)
let enc_instruction st j oc =
  let open Z3Ops in
  let enc_instr =
    match oc with
    | PUSH x -> enc_push x st j
    | ADD -> enc_add st j
    | SUB -> enc_sub st j
    | _   -> failwith "other instrs"
  in
  let enc_used_gas =
    st.used_gas @@ [j + one] == (st.used_gas @@ [j]) + (num (gas_cost oc))
  in
  enc_instr && enc_used_gas

let enc_program st =
  List.foldi ~init:(init st)
    ~f:(fun j enc oc -> enc <&> enc_instruction st (num j) oc)

let super_optimize _ = failwith "not implemented"
