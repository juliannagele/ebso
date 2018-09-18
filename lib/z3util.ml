open Core
open Z3

(* make context global for now -- if turns out badly wrap in a state monad *)
let ctxt = ref (mk_context [])

let int_sort = Arithmetic.Integer.mk_sort !ctxt
let bv_sort = BitVector.mk_sort !ctxt

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

let (~!) x = Z3.BitVector.mk_not !ctxt x

let (<@@>) fn x = FuncDecl.apply fn x

let num n = Expr.mk_numeral_int !ctxt n int_sort

let one = num 1

let bvnum n s = Expr.mk_numeral_int !ctxt n (bv_sort s)

let bvconst n s = BitVector.mk_const_s !ctxt n s

let (<<<>) x y = BitVector.mk_shl !ctxt x y
let (<>>>) x y = BitVector.mk_ashr !ctxt x y

let mk_bin_op bv_op int_op x y =
  match Sort.get_sort_kind (Expr.get_sort x), Sort.get_sort_kind (Expr.get_sort y) with
  | BV_SORT, BV_SORT -> bv_op !ctxt x y
  | INT_SORT, INT_SORT -> int_op !ctxt x y
  | _, _ -> failwith "not implemented for these sorts"

let (<+>) = mk_bin_op BitVector.mk_add (fun ctxt x y -> Arithmetic.mk_add ctxt [x; y])

let (<->) = mk_bin_op BitVector.mk_sub (fun ctxt x y -> Arithmetic.mk_sub ctxt [x; y])

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

let forall ?(weight = None) ?(patterns = []) ?(nopatterns = [])
      ?(quantifier_id = None) ?(skolem_id = None) x p =
  Quantifier.expr_of_quantifier @@
  Quantifier.mk_forall_const !ctxt [x] p
    weight patterns nopatterns quantifier_id skolem_id

let exists ?(weight = None) ?(patterns = []) ?(nopatterns = [])
      ?(quantifier_id = None) ?(skolem_id = None) x p =
  Quantifier.expr_of_quantifier @@
  Quantifier.mk_exists_const !ctxt [x] p
    weight patterns nopatterns quantifier_id skolem_id

let select a i = Z3Array.mk_select !ctxt a i


module Z3Ops = struct
  let (@@) = (<@@>)
  let (==>) x y = (<->>) x y
  let (&&) = (<&>)
  let (||) = (<|>)
  let (!) = (~!)
  let (<<) = (<<<>)
  let (>>) = (<>>>)
  let (+) = (<+>)
  let (-) = (<->)
  let (>) = (<>>)
  let (<) = (<<>)
  let (<=) = (<<=>)
  let (>=) = (<>=>)
  let (==) = (<==>)
  let (!=) = (<!=>)
end
