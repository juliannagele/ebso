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
let to_valarg c = String.chop_prefix_exn c ~prefix:"c"
let from_valarg v = "c" ^ v

type stackarg =
  | Val of valarg [@printer fun fmt x -> fprintf fmt "%s" (valarg_to_dec x)]
  | Tmpl
  | Const of constarg [@printer fun fmt x -> fprintf fmt "%s" (valarg_to_dec (to_valarg x))]
[@@deriving show { with_path = false }, sexp, compare]

let equal_stackarg x y = match (x, y) with
  | Val x, Val y -> valarg_eq x y
  | Tmpl, Tmpl -> true
  | Const c, Const d -> String.equal c d
  | _, _ -> false

let stackarg_of_sexp s = match s with
  | Sexp.Atom i -> if String.equal i "Tmpl" then Tmpl else Val i
  | Sexp.List _ -> failwith "could not parse argument of PUSH"

let all_of_stackarg = [Tmpl]

let show_stackarg_hex a =
  match a with
  | Val x -> show_valarg_hex x
  | Const c -> show_valarg_hex (to_valarg c)
  | Tmpl -> failwith "hex output not supported for template"

let mod_stackarg_to_ses ses = function
  | Tmpl -> Tmpl
  | Val i ->
    Val (Z.(mod) (Z.abs (Z.of_string i)) (Z.pow (Z.of_int 2) ses) |> Z.to_string)
  | Const c -> Const c
