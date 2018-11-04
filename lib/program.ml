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
let show_h p = pp_h Format.str_formatter p |> Format.flush_str_formatter
let show p = pp Format.str_formatter p |> Format.flush_str_formatter

let show_hex p = String.concat ~sep:"" (List.map p ~f:Instruction.show_hex)

let sis_of_progr p =
  List.map p ~f:(function | PUSH _ -> PUSH Tmpl | i -> i) |> List.stable_dedup

let stack_depth p =
  Int.abs @@ Tuple.T2.get2 @@ List.fold_left ~init:(0, 0) p
    ~f:(fun (sc, sd) is ->
        let (d, a) = delta_alpha is in (sc - d + a, min sd (sc - d)))

let total_gas_cost = List.fold ~init:0 ~f:(fun gc i -> gc + gas_cost i)

let mod_to_ses ses p = List.map p ~f:(Instruction.mod_to_ses ses)

(* basic blocks -- we classify basic blocks into 3 kinds:
- NotEncodable for instructions that are not yet supported
- Terminal if the last instruction of the block interrupts control flow,
  by JUMPing, CALLing, or interrupting execution;
- Next otherwise, i.e. control passes from the last instruction of the block
  to the first instruction of the following block
*)
type bb = Terminal of t * Instruction.t | Next of t | NotEncodable of t
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

let split_into_bbs ?(split_non_encodable=true) p =
  let is_terminal i = List.mem terminal i ~equal:Instruction.equal in
  let is_encodable i =
    match i with
    | PUSH _ -> true
    | _ -> List.mem encodable i ~equal:Instruction.equal
  in
  let rec split bb bbs = function
    | [] -> (if not (List.is_empty bb) then Next bb :: bbs else bbs) |> List.rev
    | i :: is -> match i with
      (* a terminal instruction marks the end of a BB *)
      | _ when is_terminal i ->  split [] (Terminal (bb, i) :: bbs) is
      (* when splitting at non-encodable instructions
         end current BB and collect non-encodable, non-terminal instructions *)
      | _ when not (is_encodable i) && split_non_encodable ->
        let (ne, is) =
          List.split_while (i :: is) ~f:(fun i -> not @@ (is_encodable i || is_terminal i))
        in
        let bbs = if List.is_empty bb then bbs else Next bb :: bbs in
        split [] (NotEncodable ne :: bbs) is
      (* JUMPDEST and BEGINSUB mark the beginning of a new BB *)
      | JUMPDEST | BEGINSUB -> split [i] (Next bb :: bbs) is
      | _ -> split (bb @ [i]) bbs is
  in
  split [] [] p

let rec concat_bbs = function
  | [] -> []
  | Next bb :: bbs -> bb @ concat_bbs bbs
  | Terminal (bb, i) :: bbs -> bb @ [i] @ concat_bbs bbs
  | NotEncodable bb :: bbs -> bb @ concat_bbs bbs
