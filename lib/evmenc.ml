open Core
open Z3util

(* stack address size; design decision/quick fix: the slot 2^sas - 1 is reserved
   for exception handling, otherwise the stack counter wraps around
   --> max stack size 2^sas - 1 *)
let sas = 4

(* stack element size *)
let ses = 8

type stackarg =
  | Val of int [@printer fun fmt x -> fprintf fmt "%i" x]
  | Tmpl
[@@deriving show { with_path = false }, eq]

type instr =
  | ADD
  | PUSH of stackarg
  | POP
  | SUB
[@@deriving show { with_path = false }, eq]

type progr = instr list

let delta_alpha = function
  | ADD -> (2, 1)
  | PUSH _ -> (0, 1)
  | POP -> (1, 0)
  | SUB -> (2, 1)

let stack_depth p =
  Int.abs @@ Tuple.T2.get2 @@ List.fold_left ~init:(0, 0) p
    ~f:(fun (sc, sd) is ->
        let (d, a) = delta_alpha is in (sc - d + a, min sd (sc - d)))

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

type enc_consts = {
  p : instr list;
  sis : instr list;
  kt : Z3.Expr.expr;
  fis : Z3.FuncDecl.func_decl;
  a : Z3.FuncDecl.func_decl;
  opcodes : (instr * int) list;
  xs : Z3.Expr.expr list;
}

let mk_enc_consts p sis = {
  (* source program *)
  p = p;
  (* set of potential instructions to choose from in target program *)
  sis = sis;
  (* number of instructions in target program *)
  kt = intconst "k";
  (* target program *)
  fis = func_decl "instr" [int_sort] int_sort;
  (* arguments for PUSH instrucions in target program *)
  a = func_decl "a" [int_sort] (bv_sort ses);
  (* integer encoding of opcodes *)
  opcodes = List.mapi sis ~f:(fun i oc -> (oc, i));
  (* list of free variables x_0 .. x_(stack_depth -1)
     for stack elements already on stack *)
  xs = List.init (stack_depth p)
      ~f:(fun i -> bvconst ("x_" ^ Int.to_string i) ses)
}

let enc_opcode ea i = List.Assoc.find_exn ea.opcodes ~equal:[%eq: instr] i

let dec_opcode ea i =
  List.Assoc.find_exn (List.Assoc.inverse ea.opcodes) ~equal:[%eq: int] i

let init ea st =
  let open Z3Ops in
  (* careful: if stack_depth is larger than 2^sas, no checks *)
  let skd = stack_depth (ea.p) in
  (* set stack counter to skd *)
  (st.stack_ctr @@ [num 0] == bvnum skd sas)
  (* set inital stack elements *)
  && conj (List.mapi ea.xs ~f:(fun i x -> st.stack @@ [num 0; bvnum i sas] == x))
  && (st.exc_halt @@ [num 0] == btm)
  && (st.used_gas @@ [num 0] == num 0)

(* TODO: check data layout on stack *)
let enc_stackarg ea j = function
  | Val x -> bvnum x ses
  | Tmpl -> ea.a <@@> [j]

let enc_push ea x st j =
  let open Z3Ops in
  let n = bvconst "n" sas in
  (* the stack before and after the PUSH *)
  let sk n = st.stack @@ [j; n] and sk' n = st.stack @@ [j + one; n] in
  (* the stack counter before and after the PUSH *)
  let sc = st.stack_ctr @@ [j] and sc'= st.stack_ctr @@ [j + one] in
  (* there will be one more element on the stack after PUSHing *)
  (sc' == (sc + bvnum 1 sas)) &&
  (* that element will be x *)
  sk' sc == enc_stackarg ea j x &&
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
  (sk' (sc - bvnum 2 sas) == op (sk (sc - bvnum 1 sas)) (sk (sc - bvnum 2 sas))) &&
  (* all elements below remain unchanged *)
  forall n ((n < (sc - bvnum 2 sas)) ==> (sk' n == sk n)) &&
  (* check for exceptional halting *)
  (st.exc_halt @@ [j + one] ==
  (* stack underflow occured or exceptional halting occured eariler *)
  (((sc - (bvnum 2 sas)) < (bvnum 0 sas)) || st.exc_halt @@ [j]))

let enc_add = enc_binop (<+>)
let enc_sub = enc_binop (<->)

(* effect of instruction on state st after j steps *)
let enc_instruction ea st j is =
  let open Z3Ops in
  let enc_instr =
    match is with
    | PUSH x -> enc_push ea x st j
    | ADD -> enc_add st j
    | SUB -> enc_sub st j
    | _   -> failwith "other instrs"
  in
  let enc_used_gas =
    st.used_gas @@ [j + one] == ((st.used_gas @@ [j]) + (num (gas_cost is)))
  in
  enc_instr && enc_used_gas

let enc_search_space st ea =
  let open Z3Ops in
  let j = intconst "j" in
  let enc_sis =
    List.map ea.sis ~f:(fun is ->
        (ea.fis @@ [j] == num (enc_opcode ea is)) ==> (enc_instruction ea st j is))
  in
  (* optimization potential:
     choose opcodes = 1 .. |sis| and demand fis (j) < |sis| *)
  let in_sis =
    List.map ea.sis ~f:(fun is -> ea.fis @@ [j] == num (enc_opcode ea is))
  in
  forall j (((j < ea.kt) && (j >= (num 0))) ==> conj enc_sis && disj in_sis) &&
  ea.kt >= (num 0)

(* we only demand equivalence at kt *)
let enc_equivalence sts stt ks kt =
  let open Z3Ops in
  let n = bvconst "n" sas in
  (* intially source and target stack counter are equal *)
  sts.stack_ctr @@ [num 0] == stt.stack_ctr @@ [num 0] &&
  (* initally source and target stack are equal *)
  (forall n (sts.stack @@ [num 0; n] == stt.stack @@ [num 0; n])) &&
  (* initally source and target gas are equal *)
  sts.used_gas @@ [num 0] == stt.used_gas @@ [num 0] &&
  (* after the programs have run source and target stack counter are equal *)
  sts.stack_ctr @@ [num ks] == stt.stack_ctr @@ [kt] &&
  (* after the programs have run source and target stack are equal below the stack counter *)
  (forall n ((n < stt.stack_ctr @@ [kt]) ==>
             (sts.stack @@ [num ks; n] == stt.stack @@ [kt; n]))) &&
  (* after the programs have run source and target exceptional halting are equal *)
  sts.exc_halt @@ [num ks] == stt.exc_halt @@ [kt]

let enc_program ea st =
  List.foldi ~init:(init ea st)
    ~f:(fun j enc oc -> enc <&> enc_instruction ea st (num j) oc) ea.p

let enc_super_opt ea =
  let open Z3Ops in
  let sts = mk_state "_s" in
  let stt = mk_state "_t" in
  let ks = List.length ea.p in
  foralls ea.xs
  (enc_program ea sts &&
   enc_search_space stt ea &&
   enc_equivalence sts stt ks ea.kt &&
   sts.used_gas @@ [num ks] > stt.used_gas @@ [ea.kt])

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

let eval_stack st m i n = eval_func_decl m i ~n:[bvnum n sas] st.stack

let eval_exc_halt st m i = eval_func_decl m i st.exc_halt

let eval_gas st m i = eval_func_decl m i st.used_gas

let eval_fis ea m j = eval_func_decl m j ea.fis |> Z3.Arithmetic.Integer.get_int

let eval_a ea m j = eval_func_decl m j ea.a |> Z3.Arithmetic.Integer.get_int

let dec_instr ea m j =
  let i = eval_fis ea m j |> dec_opcode ea in
  match i with
  | PUSH Tmpl -> PUSH (Val (eval_a ea m j))
  | i -> i

let dec_super_opt m ea =
  let k = Z3.Arithmetic.Integer.get_int @@ eval_const m ea.kt in
  List.init k ~f:(dec_instr ea m)

let super_optimize p sis =
  let ea = mk_enc_consts p sis in
  let c = enc_super_opt ea in
  let m = solve_model_exn [c] in
  Z3.Expr.to_string c ^ "\n\n\n" ^
  Z3.Model.to_string m ^ "\n\n" ^
  [%show: instr list] (dec_super_opt m ea)
