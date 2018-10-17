open Core
open Sedlexing
open Instruction

exception SyntaxError of int

let digit = [%sedlex.regexp? '0'..'9']
let hexdigit = [%sedlex.regexp? digit | 'a' .. 'f']
let re32 = [%sedlex.regexp? '4' .. '9' | '1' .. '2', Opt digit | '3', Opt '0' .. '2']
let re16 = [%sedlex.regexp? '2' .. '9' | '1', Opt '0' .. '6']

let parse_idx prefix s =
  let s = String.chop_prefix_exn ~prefix:prefix s in
  let idxo = idx_of_enum @@ Int.of_string s in
  Option.value_exn ~message:("parse " ^ prefix ^ " index failed") idxo

let parse buf =
  let rec parse_token acc buf =
    match%sedlex buf with
    | white_space -> parse_token acc buf
    | "ADD" -> parse_token (ADD :: acc) buf
    | "MUL" -> parse_token (MUL :: acc) buf
    | "POP" -> parse_token (POP :: acc) buf
    | "PUSH", Opt re32 -> parse_stackarg acc buf
    | "SUB" -> parse_token (SUB :: acc) buf
    | "SWAP", re16 ->
      let idx = parse_idx "SWAP" (Latin1.lexeme buf) in
      parse_token (SWAP idx :: acc) buf
    | eof -> acc
    | _ -> raise (SyntaxError (Sedlexing.lexeme_start buf))
  and parse_stackarg acc buf =
    match%sedlex buf with
    | "Tmpl" -> parse_token (PUSH Tmpl :: acc) buf
    | "0x", Plus hexdigit | Plus digit ->
      let i = Int.of_string @@ Latin1.lexeme buf in
      parse_token (PUSH (Val i) :: acc) buf
    | _ -> raise (SyntaxError (Sedlexing.lexeme_start buf))
  in
  parse_token [] buf |> List.rev
