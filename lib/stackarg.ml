open Core

(* a value argument can be either decimal, e.g., "1", hex, e.g., "0x1"
   or binary, e.g. "0b1" *)
type valarg = string [@@deriving show { with_path = false }, sexp, compare]
let valarg_to_dec x = Z.of_string x |> Z.to_string
let valarg_to_hex x = Z.of_string x |> Z.format "x"
let valarg_eq x y = Z.equal (Z.of_string x) (Z.of_string y)
let show_valarg_hex x =
  let hx = valarg_to_hex x in
  if Int.rem (String.length hx) 2 = 1 then "0" ^ hx else hx

type constarg = string [@@deriving show { with_path = false }, sexp, compare]
let constarg_to_valarg c = String.chop_prefix_exn c ~prefix:"c"
let valarg_to_constarg v = "c" ^ (valarg_to_dec v)
let constarg_eq = String.equal
let constarg_to_dec = constarg_to_valarg (* convention is that constarg is in dec *)
let show_constarg_hex c = show_valarg_hex (constarg_to_valarg c)

type t =
  | Val of valarg [@printer fun fmt x -> fprintf fmt "%s" (valarg_to_dec x)]
  | Tmpl
  | Const of constarg [@printer fun fmt x -> fprintf fmt "%s" (constarg_to_dec x)]
[@@deriving show { with_path = false }, sexp, compare]

let equal x y = match (x, y) with
  | Val x, Val y -> valarg_eq x y
  | Tmpl, Tmpl -> true
  | Const c, Const d -> constarg_eq c d
  | _, _ -> false

let of_sexp s = match s with
  | Sexp.Atom i -> if String.equal i "Tmpl" then Tmpl else Val i
  | Sexp.List _ -> failwith "could not parse argument of PUSH"

let all = [Tmpl]

let show_stackarg_hex a =
  match a with
  | Val x -> show_valarg_hex x
  | Const c -> show_constarg_hex c
  | Tmpl -> failwith "hex output not supported for template"

let val_to_const ses a =
  let max_repr = Z.pow (Z.of_int 2) ses in
  match a with
  | Val x -> if Z.of_string x >= max_repr then Const (valarg_to_constarg x) else a
  | a -> a

let const_to_val = function
  | Const c -> Val (constarg_to_valarg c)
  | a -> a
