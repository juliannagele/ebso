open Core

type stackarg =
  | Val of int [@printer fun fmt x -> fprintf fmt "%i" x]
  | Tmpl
[@@deriving show { with_path = false }, eq, sexp]

let stackarg_of_sexp s = match s with
  | Sexp.Atom i -> if String.equal i "Tmpl" then Tmpl else Val (Int.of_string i)
  | Sexp.List _ -> failwith "could not parse argument of PUSH"

let all_of_stackarg = [Tmpl]

type idx =
  | I [@value 1] | II | III | IV | V
  | VI | VII | VIII | IX | X
  | XI | XII | XIII | XIV | XV | XVI
[@@deriving show { with_path = false }, eq, enum, enumerate, sexp]

type t =
  | ADD
  | MUL
  | PUSH of stackarg [@printer fun fmt x -> fprintf fmt "PUSH %s" (show_stackarg x)]
  | POP
  | SUB
  | SWAP of idx
[@@deriving show { with_path = false }, eq, enumerate, sexp]

let delta_alpha = function
  | ADD -> (2, 1)
  | MUL -> (2, 1)
  | PUSH _ -> (0, 1)
  | POP -> (1, 0)
  | SUB -> (2, 1)
  | SWAP i -> (idx_to_enum i + 1, idx_to_enum i + 1)

let gas_cost = function
  | ADD -> 3
  | MUL -> 5
  | PUSH _ -> 3
  | POP -> 2
  | SUB -> 3
  | SWAP _ -> 3
