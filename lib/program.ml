open Core
open Instruction

type t = Instruction.t list [@@deriving show, eq, sexp]

let sis_of_progr p =
  List.map p ~f:(function | PUSH _ -> PUSH Tmpl | i -> i) |> List.stable_dedup

let stack_depth p =
  Int.abs @@ Tuple.T2.get2 @@ List.fold_left ~init:(0, 0) p
    ~f:(fun (sc, sd) is ->
        let (d, a) = delta_alpha is in (sc - d + a, min sd (sc - d)))

let total_gas_cost = List.fold ~init:0 ~f:(fun gc i -> gc + gas_cost i)
