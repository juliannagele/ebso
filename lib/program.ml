open Core
open Instruction

type t = Instruction.t list [@@deriving eq, sexp]

let rec pp_aux frmt fmt = function
  | [] -> ()
  | [i] -> Format.fprintf fmt "%a" Instruction.pp i
  | i :: is -> Format.fprintf fmt frmt Instruction.pp i (pp_aux frmt) is
let pp_h fmt p =
  Format.fprintf fmt "@[<h>";
  pp_aux "%a@ %a" fmt p;
  Format.fprintf fmt "@]"
let pp_v fmt p =
  Format.fprintf fmt "@,@[<v>";
  pp_aux "%a@,%a" fmt p;
  Format.fprintf fmt "@]"
let pp_ocamllist fmt p =
  Format.fprintf fmt "@[<hov>[";
  pp_aux "%a;@ %a" fmt p;
  Format.fprintf fmt "]@]"
let pp = pp_v
let show p = pp Format.str_formatter p |> Format.flush_str_formatter

let sis_of_progr p =
  List.map p ~f:(function | PUSH _ -> PUSH Tmpl | i -> i) |> List.stable_dedup

let stack_depth p =
  Int.abs @@ Tuple.T2.get2 @@ List.fold_left ~init:(0, 0) p
    ~f:(fun (sc, sd) is ->
        let (d, a) = delta_alpha is in (sc - d + a, min sd (sc - d)))

let total_gas_cost = List.fold ~init:0 ~f:(fun gc i -> gc + gas_cost i)
