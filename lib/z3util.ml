open Core
open Z3

(* make context global for now -- if turns out badly wrap in a state monad *)
let ctxt = ref (mk_context [])

let int_sort = Arithmetic.Integer.mk_sort !ctxt
let bv_sort = BitVector.mk_sort !ctxt
let bool_sort = Boolean.mk_sort !ctxt

let num n = Expr.mk_numeral_int !ctxt n int_sort
let one = num 1
let bvnum n size = Expr.mk_numeral_int !ctxt n (bv_sort size)
let bvconst = BitVector.mk_const_s !ctxt
let intconst = Arithmetic.Integer.mk_const_s !ctxt
let func_decl = FuncDecl.mk_func_decl_s !ctxt
let boolconst = Boolean.mk_const_s !ctxt
let top = Boolean.mk_true !ctxt
let btm = Boolean.mk_false !ctxt

let (<->>) x y =
  if Boolean.is_true x then y
  else if Boolean.is_false x then Boolean.mk_true !ctxt
  else Boolean.mk_implies !ctxt x y

let conj = function
  | [] -> Boolean.mk_true !ctxt
  | [x] -> x
  | _ as xs -> Boolean.mk_and !ctxt xs

let (<&>) x y = conj [x; y]

let disj = function
  | [] -> Boolean.mk_false !ctxt
  | [x] -> x
  | _ as xs -> Boolean.mk_or !ctxt xs

let (<|>) x y = disj [x; y]

let (~!) x =
  match Sort.get_sort_kind (Expr.get_sort x) with
  | BV_SORT -> BitVector.mk_not !ctxt x
  | BOOL_SORT -> Boolean.mk_not !ctxt x
  | _ -> failwith "not implemented for this sort"

let ite = Boolean.mk_ite !ctxt

let (<@@>) fn x = FuncDecl.apply fn x

let (<<<>) x y = BitVector.mk_shl !ctxt x y
let (<>>>) x y = BitVector.mk_ashr !ctxt x y

let mk_bin_op bv_op int_op x y =
  match Sort.get_sort_kind (Expr.get_sort x), Sort.get_sort_kind (Expr.get_sort y) with
  | BV_SORT, BV_SORT -> bv_op !ctxt x y
  | INT_SORT, INT_SORT -> int_op !ctxt x y
  | _, _ -> failwith "not implemented for these sorts"

let (<+>) = mk_bin_op BitVector.mk_add (fun ctxt x y -> Arithmetic.mk_add ctxt [x; y])

let (<->) = mk_bin_op BitVector.mk_sub (fun ctxt x y -> Arithmetic.mk_sub ctxt [x; y])

let (<*>) = mk_bin_op BitVector.mk_mul (fun ctxt x y -> Arithmetic.mk_mul ctxt [x; y])

let udiv = BitVector.mk_udiv !ctxt
let umod = BitVector.mk_urem !ctxt
let srem = BitVector.mk_srem !ctxt

let zeroext k bv = Z3.BitVector.mk_zero_ext !ctxt k bv

let extract h l = Z3.BitVector.mk_extract !ctxt h l

let no_overflow is_signed op1 op2 = function
  | `Add -> BitVector.mk_add_no_overflow !ctxt op1 op2 is_signed
  | `Sub -> BitVector.mk_sub_no_overflow !ctxt op1 op2
  | `Mul -> BitVector.mk_mul_no_overflow !ctxt op1 op2 is_signed

let nsw op1 op2 = no_overflow true op1 op2
let nuw op1 op2 = no_overflow false op1 op2

let (<<>) = mk_bin_op BitVector.mk_slt Arithmetic.mk_lt
let (<>>) = mk_bin_op BitVector.mk_sgt Arithmetic.mk_gt
let (<>=>) = mk_bin_op BitVector.mk_sge Arithmetic.mk_ge
let (<<=>) = mk_bin_op BitVector.mk_sle Arithmetic.mk_le

let (<!=>) x y = Boolean.mk_distinct !ctxt [x; y]
let (<==>) x y = Boolean.mk_eq !ctxt x y

let foralls ?(weight = None) ?(patterns = []) ?(nopatterns = [])
    ?(quantifier_id = None) ?(skolem_id = None) xs p =
  if List.is_empty xs then p else
  Quantifier.expr_of_quantifier @@
  Quantifier.mk_forall_const !ctxt xs p
    weight patterns nopatterns quantifier_id skolem_id

let forall ?(weight = None) ?(patterns = []) ?(nopatterns = [])
    ?(quantifier_id = None) ?(skolem_id = None) x p =
  foralls ~weight ~patterns ~nopatterns ~quantifier_id ~skolem_id [x] p

let existss ?(weight = None) ?(patterns = []) ?(nopatterns = [])
    ?(quantifier_id = None) ?(skolem_id = None) xs p =
  if List.is_empty xs then p else
  Quantifier.expr_of_quantifier @@
  Quantifier.mk_exists_const !ctxt xs p
    weight patterns nopatterns quantifier_id skolem_id

let exists ?(weight = None) ?(patterns = []) ?(nopatterns = [])
    ?(quantifier_id = None) ?(skolem_id = None) x p =
  existss ~weight ~patterns ~nopatterns ~quantifier_id ~skolem_id [x] p

let select a i = Z3Array.mk_select !ctxt a i

let solve_model_exn cs =
  let slvr = Solver.mk_solver !ctxt None in
  let () = Solver.add slvr cs in
  match Solver.check slvr [] with
  | Solver.SATISFIABLE ->
    begin
      match Solver.get_model slvr with
      | Some m -> m
      | None -> failwith "SAT but no model"
    end
  | Solver.UNSATISFIABLE -> failwith "UNSAT"
  | Solver.UNKNOWN -> failwith (Solver.get_reason_unknown slvr)

let eval_func_decl m j ?(n = []) ?(xs = []) f =
  match Z3.Model.eval m (f <@@> (xs @ [num j] @ n)) true with
  | Some e -> e
  | None -> failwith ("could not eval " ^ Z3.FuncDecl.to_string f)

let eval_const m k =
  match Z3.Model.eval m k true with
  | Some e -> e
  | None -> failwith ("could not eval " ^ Z3.Expr.to_string k)

module Z3Ops = struct
  let (@@) = (<@@>)
  let (==>) x y = (<->>) x y
  let (&&) = (<&>)
  let (||) = (<|>)
  let (~!) = (~!)
  let (<<) = (<<<>)
  let (>>) = (<>>>)
  let (+) = (<+>)
  let (-) = (<->)
  let ( * ) = (<*>)
  let (>) = (<>>)
  let (<) = (<<>)
  let (<=) = (<<=>)
  let (>=) = (<>=>)
  let (==) = (<==>)
  let (!=) = (<!=>)
end
