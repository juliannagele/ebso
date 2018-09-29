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
[@@deriving show { with_path = false }, eq]

type progr = instr list

let opcodes =
  [ (ADD, 0)
  ; (PUSH 1, 1)
  ; (PUSH 2, 2)
  ; (POP, 3)
  ; (SUB, 4)
  ]

let enc_opcode = List.Assoc.find_exn opcodes ~equal:[%eq: instr]
let dec_opcode = List.Assoc.find_exn (List.Assoc.inverse opcodes) ~equal:[%eq: int]

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

let mk_state idx = {
  (* stack(j, n) = nth stack element after j instructions *)
  stack = func_decl ("stack" ^ idx) [int_sort; bv_sort sas] (bv_sort ses);
  (* sc(j) = index of the next free slot on the stack after j instructions *)
  stack_ctr = func_decl ("sc" ^ idx) [int_sort] (bv_sort sas);
  (* exc_halt(j) is true if exceptional halting occurs after j instructions *)
  exc_halt = func_decl ("exc_halt" ^ idx) [int_sort] bool_sort;
  (* gas(j) = amount of gas used to execute the first j instructions *)
  used_gas = func_decl ("used_gas" ^ idx) [int_sort] int_sort;
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
  ((sc - (bvnum 2 sas)) < (bvnum 0 sas)) || st.exc_halt @@ [j])

let enc_add = enc_binop (<+>)
let enc_sub = enc_binop (<->)

(* effect of instruction on state st after j steps *)
let enc_instruction st j is =
  let open Z3Ops in
  let enc_instr =
    match is with
    | PUSH x -> enc_push x st j
    | ADD -> enc_add st j
    | SUB -> enc_sub st j
    | _   -> failwith "other instrs"
  in
  let enc_used_gas =
    st.used_gas @@ [j + one] == (st.used_gas @@ [j]) + (num (gas_cost is))
  in
  enc_instr && enc_used_gas

let enc_search_space st k sis fis =
  let open Z3Ops in
  let j = intconst "j" in
  let enc_sis =
    List.map sis ~f:(fun is ->
        (fis @@ [j] == num (enc_opcode is)) ==> (enc_instruction st j is))
  in
  (* optimization potential:
     choose opcodes = 1 .. |sis| and demand fis (j) < |sis| *)
  let in_sis =
    List.map sis ~f:(fun is -> fis @@ [j] == num (enc_opcode is))
  in
  forall j (((j < k) && (j >= (num 0))) ==> conj enc_sis && disj in_sis) &&
  k >= (num 0)

(* we only demand equivalence at kt *)
let enc_equivalence sts stt ks kt =
  let open Z3Ops in
  let n = bvconst "n" sas in
  (forall n (sts.stack @@ [num 0; n] == stt.stack @@ [num 0; n])) &&
  sts.stack_ctr @@ [num ks] == stt.stack_ctr @@ [kt] &&
  (forall n ((n < stt.stack_ctr @@ [kt]) ==>
     (sts.stack @@ [num ks; n] == stt.stack @@ [kt; n]))) &&
  sts.exc_halt @@ [num ks] == stt.exc_halt @@ [kt]

let enc_program st =
  List.foldi ~init:(init st)
    ~f:(fun j enc oc -> enc <&> enc_instruction st (num j) oc)

let enc_super_opt p =
  let open Z3Ops in
  let sts = mk_state "_s" in
  let stt = mk_state "_t" in
  let ks = List.length p in
  let kt = intconst "k" in
  let fis = func_decl "instr" [int_sort] int_sort in
  let sis = [PUSH 2] in
  enc_program sts p &&
  enc_search_space stt kt sis fis &&
  enc_equivalence sts stt ks kt

let solve_model_exn cs =
  let slvr = Z3.Solver.mk_simple_solver !ctxt in
  let () = Z3.Solver.add slvr cs in
  match Z3.Solver.check slvr [] with
  | Z3.Solver.SATISFIABLE ->
    begin
      match Z3.Solver.get_model slvr with
      | Some m -> m
      | None -> failwith "SAT but no model"
    end
  | Z3.Solver.UNSATISFIABLE -> failwith "UNSAT"
  | Z3.Solver.UNKNOWN -> failwith (Z3.Solver.get_reason_unknown slvr)

let eval_func_decl_at_i m i ?(n = []) f =
  match Z3.Model.eval m (f <@@> ([num i] @ n)) true with
  | Some e -> e
  | None -> failwith ("could not eval " ^ Z3.FuncDecl.to_string f)

let eval_stack st m i n = eval_func_decl_at_i m i ~n:[bvnum n sas] st.stack

let eval_exc_halt st m i = eval_func_decl_at_i m i st.exc_halt

let eval_gas st m i = eval_func_decl_at_i m i st.used_gas

let eval_const m k =
  match Z3.Model.eval m k true with
  | Some e -> e
  | None -> failwith ("could not eval " ^ Z3.Expr.to_string k)

let dec_super_opt m k fis =
  let k = Z3.Arithmetic.Integer.get_int @@ eval_const m k in
  List.init k
    ~f:(fun j -> eval_func_decl_at_i m j fis
                 |> Z3.Arithmetic.Integer.get_int |> dec_opcode)

let super_optimize p =
  let c = enc_super_opt p in
  let slvr = Z3.Solver.mk_simple_solver !ctxt in
  let () = Z3.Solver.add slvr [c] in
  match Z3.Solver.check slvr [] with
  | Z3.Solver.SATISFIABLE ->
    begin
      match Z3.Solver.get_model slvr with
      | Some m -> Z3.Expr.to_string c ^ "\n\n\n" ^ Z3.Model.to_string m
      | None -> failwith "SAT but no model"
    end
  | Z3.Solver.UNSATISFIABLE -> failwith "UNSAT"
  | Z3.Solver.UNKNOWN -> failwith (Z3.Solver.get_reason_unknown slvr)
