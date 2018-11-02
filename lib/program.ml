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
  Format.fprintf fmt "@]@,"
let pp_ocamllist fmt p =
  Format.fprintf fmt "@[<hov>[";
  pp_aux "%a;@ %a" fmt p;
  Format.fprintf fmt "]@]"
let pp_sexplist fmt p = sexp_of_t p |> Sexp.pp fmt
let pp = pp_v
let show p = pp Format.str_formatter p |> Format.flush_str_formatter

let sis_of_progr p =
  List.map p ~f:(function | PUSH _ -> PUSH Tmpl | i -> i) |> List.stable_dedup

let stack_depth p =
  Int.abs @@ Tuple.T2.get2 @@ List.fold_left ~init:(0, 0) p
    ~f:(fun (sc, sd) is ->
        let (d, a) = delta_alpha is in (sc - d + a, min sd (sc - d)))

let total_gas_cost = List.fold ~init:0 ~f:(fun gc i -> gc + gas_cost i)

(* basic blocks -- we classify basic blocks into 2 kinds:
- Terminal if the last instruction of the block interrupts control flow,
  by JUMPing, CALLing, or interrupting execution;
- Next otherwise, i.e. control passes from the last instruction of the block
  to the first instruction of the following block *)
type bb = Terminal of t * Instruction.t | Next of t
[@@deriving show {with_path = false}, eq]

(* instructions that terminate a basic block *)
let terminal =
  [ STOP
  ; JUMP
  ; JUMPI
  ; JUMPTO
  ; JUMPV
  ; JUMPSUB
  ; JUMPSUBV
  ; RETURNSUB
  ; CREATE
  ; CALL
  ; CALLCODE
  ; RETURN
  ; DELEGATECALL
  ; CREATE2
  ; STATICCALL
  ; REVERT
  ; INVALID
  ; SELFDESTRUCT
  ]

let split_into_bbs p =
  let rec split bb bbs = function
    | [] -> (if not (List.is_empty bb) then Next bb :: bbs else bbs) |> List.rev
    | i :: is -> match i with
      (* JUMPDEST and BEGINSUB mark the beginning of a new BB *)
      | JUMPDEST | BEGINSUB -> split [i] (Next bb :: bbs) is
      (* an instruction in terminal marks the end of a BB *)
      | _ when List.mem terminal i ~equal:Instruction.equal ->
        split [] (Terminal (bb, i) :: bbs) is
      | _ -> split (bb @ [i]) bbs is
  in
  split [] [] p

let rec concat_bbs = function
  | [] -> []
  | Next bb :: bbs -> bb @ concat_bbs bbs
  | Terminal (bb, i) :: bbs -> bb @ [i] @ concat_bbs bbs
