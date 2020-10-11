(*   Copyright 2018 Julian Nagele and Maria A Schett

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)
open Core
open Instruction.T

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

let cis_of_progr p =
  List.map p ~f:(function | PUSH _ -> PUSH Tmpl | i -> i) |> List.stable_dedup

let stack_depth p =
  Int.abs @@ Tuple.T2.get2 @@ List.fold_left ~init:(0, 0) p
    ~f:(fun (sc, sd) is ->
        let (d, a) = Instruction.delta_alpha is in (sc - d + a, min sd (sc - d)))

let total_gas_cost =
  let open Gas_cost in
  List.fold ~init:zero ~f:(fun gc i -> gc + Instruction.gas_cost i)

let val_to_const wsz p =
  let fit w = if Word.fits_wsz wsz w then w else Word.to_const w in
  List.map p
    ~f:(function | PUSH (Word w) -> PUSH (Word (fit w)) | i -> i)

let const_to_val p =
  List.map p
    ~f:(function | PUSH (Word w) -> PUSH (Word (Word.to_val w)) | i -> i)

let consts p = List.stable_dedup
    (List.filter_map p ~f:(function | PUSH (Word (Const c)) -> Some c | _ -> None))

let compute_word_size p max_ws =
  let uc =
    List.filter p ~f:Instruction.is_uninterpreted
    |> List.partition_tf ~f:Instruction.is_const
    |> Tuple.T2.map_fst ~f:List.stable_dedup
    |> fun (c, nc) -> List.length c + List.length nc
  in
  let d = stack_depth p in
  let abstr_vals ws =
    List.count p
      ~f:(function PUSH (Word (Val x)) -> Word.numbits (Val x) > ws | _ -> false)
  in
  let rec get_min_ws n m =
    if n <= 0 then m else
      let an = abstr_vals n and am = abstr_vals m in
      let nb = (an + d + uc) * n and mb = (am + d + uc) * m in
      let m = match Int.compare nb mb with
        | -1 -> n
        | 0 when an <= am -> n
        | _ -> m
      in
      get_min_ws (n - 1) m
  in get_min_ws (max_ws - 1) max_ws

(* basic blocks -- we classify basic blocks into 3 kinds:
- NotEncodable for instructions that are not yet supported
- Terminal if the last instruction of the block interrupts control flow,
  by JUMPing, CALLing, or interrupting execution;
- Next otherwise, i.e. control passes from the last instruction of the block
  to the first instruction of the following block
*)
type bb = Terminal of t * Instruction.t | Next of t | NotEncodable of t
[@@deriving show {with_path = false}, eq]

let ebso_snippet = function
  | Terminal (p, _) -> Some p
  | Next p -> Some p
  | _ -> None

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
    | _ -> List.mem (Instruction.encodable @ Instruction.uninterpreted) i ~equal:Instruction.equal
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

let rec enumerate g cis m = match Int.Map.find m g with
  | Some ps -> (ps, m)
  | None ->
    let pgs = List.init g ~f:Fn.id in
    let (ps, m') =
      List.fold_left pgs ~init:([], m) ~f:(fun (ps, m) pg ->
          let is =
            List.filter cis ~f:(fun i ->
                Gas_cost.equal (Instruction.gas_cost i) (Gas_cost.of_int (g - pg)))
          in
          let (pps, m') = enumerate pg cis m in
          let addi pp i = List.sort ~compare:Instruction.compare (i :: pp) in
          (List.concat_map pps ~f:(fun pp -> List.map is ~f:(addi pp)) @ ps, m'))
    in
    let ps = List.stable_dedup ps in
    (ps, Int.Map.add_exn m' ~key:g ~data:ps)

let poss_of_instr p i =
  List.filter_mapi p ~f:(fun pos i' ->
      if Instruction.equal i i'
      then Some (Program_counter.of_int pos)
      else None)

let length p = Program_counter.of_int (List.length p)

let init l ~f:f =
  List.init (Program_counter.to_int l) ~f:(fun i -> f (Program_counter.of_int i))
