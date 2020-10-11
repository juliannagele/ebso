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
open Sedlexing
open Pusharg
open Instruction.T

exception SyntaxError of int
exception Eof

let digit = [%sedlex.regexp? '0'..'9']
let hexdigit = [%sedlex.regexp? digit | 'a' .. 'f']
let re32 = [%sedlex.regexp? '4' .. '9' | '1' .. '2', Opt digit | '3', Opt '0' .. '2']
let re16 = [%sedlex.regexp? '2' .. '9' | '1', Opt '0' .. '6']
let reXVI = [%sedlex.regexp? 'I',Opt('I'|"II"|'V'|'X') | 'V',Opt('I'|"II"|"III") | 'X',Opt('I'|"II"|"III"|"IV"|"V"|"VI")]
let white_spaces = [%sedlex.regexp? Star white_space]

let parse_idx prefix s =
  let s = String.chop_prefix_exn ~prefix:prefix s in
  let idxo = Instruction.idx_of_enum @@ Int.of_string s in
  Option.value_exn ~message:("parse " ^ prefix ^ " index failed") idxo

let parse_idxI prefix s =
  let s = String.chop_prefix_exn ~prefix:prefix s in
  Instruction.idx_of_sexp (Atom s)

let rec parse_pusharg buf =
  match%sedlex buf with
  | white_space -> parse_pusharg buf
  | "Tmpl" -> Tmpl
  | "0x", Plus hexdigit | Plus digit -> Word (Word.from_string (Latin1.lexeme buf))
  | _ -> raise (SyntaxError (lexeme_start buf))

let parse_instruction parse_pusharg buf =
  match%sedlex buf with
  | "STOP" -> STOP
  | "ADD" -> ADD
  | "MUL" -> MUL
  | "SUB" -> SUB
  | "DIV" -> DIV
  | "SDIV" -> SDIV
  | "MOD" -> MOD
  | "SMOD" -> SMOD
  | "ADDMOD" -> ADDMOD
  | "MULMOD" -> MULMOD
  | "EXP" -> EXP
  | "SIGNEXTEND" -> SIGNEXTEND
  | "LT" -> LT
  | "GT" -> GT
  | "SLT" -> SLT
  | "SGT" -> SGT
  | "EQ" -> EQ
  | "ISZERO" -> ISZERO
  | "AND" -> AND
  | "OR" -> OR
  | "XOR" -> XOR
  | "NOT" -> NOT
  | "BYTE" -> BYTE
  | "SHL" -> SHL
  | "SHR" -> SHR
  | "SAR" -> SAR
  | "SHA3" -> SHA3
  | "ADDRESS" -> ADDRESS
  | "BALANCE" -> BALANCE
  | "ORIGIN" -> ORIGIN
  | "CALLER" -> CALLER
  | "CALLVALUE" -> CALLVALUE
  | "CALLDATALOAD" -> CALLDATALOAD
  | "CALLDATASIZE" -> CALLDATASIZE
  | "CALLDATACOPY" -> CALLDATACOPY
  | "CODESIZE" -> CODESIZE
  | "CODECOPY" -> CODECOPY
  | "GASPRICE" -> GASPRICE
  | "EXTCODESIZE" -> EXTCODESIZE
  | "EXTCODECOPY" -> EXTCODECOPY
  | "RETURNDATASIZE" -> RETURNDATASIZE
  | "RETURNDATACOPY" -> RETURNDATACOPY
  | "EXTCODEHASH" -> EXTCODEHASH
  | "BLOCKHASH" -> BLOCKHASH
  | "COINBASE" -> COINBASE
  | "TIMESTAMP" -> TIMESTAMP
  | "NUMBER" -> NUMBER
  | "DIFFICULTY" -> DIFFICULTY
  | "GASLIMIT" -> GASLIMIT
  | "POP" -> POP
  | "MLOAD" -> MLOAD
  | "MSTORE" -> MSTORE
  | "MSTORE8" -> MSTORE8
  | "SLOAD" -> SLOAD
  | "SSTORE" -> SSTORE
  | "JUMP" -> JUMP
  | "JUMPI" -> JUMPI
  | "PC" -> PC
  | "MSIZE" -> MSIZE
  | "GAS" -> GAS
  | "JUMPDEST" -> JUMPDEST
  | "PUSH", Opt re32 -> PUSH (parse_pusharg buf)
  | "DUP", re16 -> DUP (parse_idx "DUP" (Latin1.lexeme buf))
  | "DUP ", reXVI -> DUP (parse_idxI "DUP " (Latin1.lexeme buf))
  | "SWAP", re16 -> SWAP (parse_idx "SWAP" (Latin1.lexeme buf))
  | "SWAP ", reXVI -> SWAP (parse_idxI "SWAP " (Latin1.lexeme buf))
  | "LOG0" -> LOG0
  | "LOG1" -> LOG1
  | "LOG2" -> LOG2
  | "LOG3" -> LOG3
  | "LOG4" -> LOG4
  | "JUMPTO" -> JUMPTO
  | "JUMPIF" -> JUMPIF
  | "JUMPV" -> JUMPV
  | "JUMPSUB" -> JUMPSUB
  | "JUMPSUBV" -> JUMPSUBV
  | "BEGINSUB" -> BEGINSUB
  | "BEGINDATA" -> BEGINDATA
  | "RETURNSUB" -> RETURNSUB
  | "PUTLOCAL" -> PUTLOCAL
  | "GETLOCAL" -> GETLOCAL
  | "CREATE" -> CREATE
  | "CALL" -> CALL
  | "CALLCODE" -> CALLCODE
  | "RETURN" -> RETURN
  | "DELEGATECALL" -> DELEGATECALL
  | "CREATE2" -> CREATE2
  | "STATICCALL" -> STATICCALL
  | "REVERT" -> REVERT
  | "INVALID" -> INVALID
  | "SELFDESTRUCT" -> SELFDESTRUCT
  | _ -> raise (SyntaxError (lexeme_start buf))

let parse_hex_idx s n =
  let idxo = Instruction.idx_of_enum @@ Int.of_string ("0x" ^ s) - n in
  Option.value_exn ~message:("parse hex index failed") idxo

let parse_hex_bytes n buf =
  let rec parse_hex_bytes n acc =
    if n <= 0 then acc
    else
      match%sedlex buf with
      | Rep (hexdigit, 2) -> parse_hex_bytes (n - 1) (acc ^ Latin1.lexeme buf)
      | eof -> raise Eof
      | _ -> raise (SyntaxError (lexeme_start buf))
  in
  parse_hex_bytes n "0x"

let parse_hex ?(ignore_data_section=false) buf =
  let rec parse_token acc =
    match%sedlex buf with
    (* solc adds hash of contract metadata behin conract like so:
       0xa1 0x65 'b' 'z' 'z' 'r' '0' 0x58 0x20 <32 bytes swarm hash> 0x00 0x29 *)
    | "a165627a7a72305820", Rep (hexdigit, 64), "0029" -> parse_token acc
    | "00" -> parse_token (STOP :: acc)
    | "01" -> parse_token (ADD :: acc)
    | "02" -> parse_token (MUL :: acc)
    | "03" -> parse_token (SUB :: acc)
    | "04" -> parse_token (DIV :: acc)
    | "05" -> parse_token (SDIV :: acc)
    | "06" -> parse_token (MOD :: acc)
    | "07" -> parse_token (SMOD :: acc)
    | "08" -> parse_token (ADDMOD :: acc)
    | "09" -> parse_token (MULMOD :: acc)
    | "0a" -> parse_token (EXP :: acc)
    | "0b" -> parse_token (SIGNEXTEND :: acc)
    | "10" -> parse_token (LT :: acc)
    | "11" -> parse_token (GT :: acc)
    | "12" -> parse_token (SLT :: acc)
    | "13" -> parse_token (SGT :: acc)
    | "14" -> parse_token (EQ :: acc)
    | "15" -> parse_token (ISZERO :: acc)
    | "16" -> parse_token (AND :: acc)
    | "17" -> parse_token (OR :: acc)
    | "18" -> parse_token (XOR :: acc)
    | "19" -> parse_token (NOT :: acc)
    | "1a" -> parse_token (BYTE :: acc)
    | "1b" -> parse_token (SHL :: acc)
    | "1c" -> parse_token (SHR :: acc)
    | "1d" -> parse_token (SAR :: acc)
    | "20" -> parse_token (SHA3 :: acc)
    | "30" -> parse_token (ADDRESS :: acc)
    | "31" -> parse_token (BALANCE :: acc)
    | "32" -> parse_token (ORIGIN :: acc)
    | "33" -> parse_token (CALLER :: acc)
    | "34" -> parse_token (CALLVALUE :: acc)
    | "35" -> parse_token (CALLDATALOAD :: acc)
    | "36" -> parse_token (CALLDATASIZE :: acc)
    | "37" -> parse_token (CALLDATACOPY :: acc)
    | "38" -> parse_token (CODESIZE :: acc)
    | "39" -> parse_token (CODECOPY :: acc)
    | "3a" -> parse_token (GASPRICE :: acc)
    | "3b" -> parse_token (EXTCODESIZE :: acc)
    | "3c" -> parse_token (EXTCODECOPY :: acc)
    | "3d" -> parse_token (RETURNDATASIZE :: acc)
    | "3e" -> parse_token (RETURNDATACOPY :: acc)
    | "3f" -> parse_token (EXTCODEHASH :: acc)
    | "40" -> parse_token (BLOCKHASH :: acc)
    | "41" -> parse_token (COINBASE :: acc)
    | "42" -> parse_token (TIMESTAMP :: acc)
    | "43" -> parse_token (NUMBER :: acc)
    | "44" -> parse_token (DIFFICULTY :: acc)
    | "45" -> parse_token (GASLIMIT :: acc)
    | "50" -> parse_token (POP :: acc)
    | "51" -> parse_token (MLOAD :: acc)
    | "52" -> parse_token (MSTORE :: acc)
    | "53" -> parse_token (MSTORE8 :: acc)
    | "54" -> parse_token (SLOAD :: acc)
    | "55" -> parse_token (SSTORE :: acc)
    | "56" -> parse_token (JUMP :: acc)
    | "57" -> parse_token (JUMPI :: acc)
    | "58" -> parse_token (PC :: acc)
    | "59" -> parse_token (MSIZE :: acc)
    | "5a" -> parse_token (GAS :: acc)
    | "5b" -> parse_token (JUMPDEST :: acc)
    | ('6' | '7'), hexdigit ->
      begin
        (* 0x60 = 96, so x in PUSHx is 0x<lexeme> - 95 *)
        let n = Int.of_string ("0x" ^ Latin1.lexeme buf) - 95 in
        try
          let i = parse_hex_bytes n buf in
          parse_token (PUSH (Word (Word.from_string i)) :: acc)
        with Eof ->
          if ignore_data_section then
            List.drop_while acc ~f:(fun i -> not (Instruction.equal i STOP))
          else raise (SyntaxError (lexeme_start buf))
      end
    | '8', hexdigit ->
      (* 0x80 = 128, so x in DUPx is 0x<lexeme> - 127 *)
      let idx = parse_hex_idx (Latin1.lexeme buf) 127 in
      parse_token (DUP idx :: acc)
    | '9', hexdigit ->
      (* 0x90 = 144, so x in SWAPx is 0x<lexeme> - 143 *)
      let idx = parse_hex_idx (Latin1.lexeme buf) 143 in
      parse_token (SWAP idx :: acc)
    | "a0" -> parse_token (LOG0 :: acc)
    | "a1" -> parse_token (LOG1 :: acc)
    | "a2" -> parse_token (LOG2 :: acc)
    | "a3" -> parse_token (LOG3 :: acc)
    | "a4" -> parse_token (LOG4 :: acc)
    | "b0" -> parse_token (JUMPTO :: acc)
    | "b1" -> parse_token (JUMPIF :: acc)
    | "b2" -> parse_token (JUMPV :: acc)
    | "b3" -> parse_token (JUMPSUB :: acc)
    | "b4" -> parse_token (JUMPSUBV :: acc)
    | "b5" -> parse_token (BEGINSUB :: acc)
    | "b6" -> parse_token (BEGINDATA :: acc)
    | "b7" -> parse_token (RETURNSUB :: acc)
    | "b8" -> parse_token (PUTLOCAL :: acc)
    | "b9" -> parse_token (GETLOCAL :: acc)
    | "f0" -> parse_token (CREATE :: acc)
    | "f1" -> parse_token (CALL :: acc)
    | "f2" -> parse_token (CALLCODE :: acc)
    | "f3" -> parse_token (RETURN :: acc)
    | "f4" -> parse_token (DELEGATECALL :: acc)
    | "f5" -> parse_token (CREATE2 :: acc)
    | "fa" -> parse_token (STATICCALL :: acc)
    | "fd" -> parse_token (REVERT :: acc)
    | "fe" -> parse_token (INVALID :: acc)
    | "ff" -> parse_token (SELFDESTRUCT :: acc)
    | white_spaces, eof -> acc
    | _ ->
      if ignore_data_section then
        List.drop_while acc ~f:(fun i -> not (Instruction.equal i STOP))
      else
        raise (SyntaxError (lexeme_start buf))
  in
  parse_token [] |> List.rev

let parse_wslist parse_pusharg buf =
  let parse_instruction = parse_instruction parse_pusharg in
  let rec parse_wslist acc =
    match%sedlex buf with
    | white_spaces, eof -> List.rev acc
    | white_spaces -> parse_wslist (parse_instruction buf :: acc)
    | _ -> raise (SyntaxError (lexeme_start buf))
  in
  parse_wslist []

let parse ?(ignore_data_section=false) buf =
  let parse_instruction = parse_instruction parse_pusharg in
  let rec parse_ocamllist acc =
    match%sedlex buf with
    | white_spaces, ';', white_spaces ->
      parse_ocamllist (parse_instruction buf :: acc)
    | ']', white_spaces, eof -> List.rev acc
    | _ -> raise (SyntaxError (lexeme_start buf))
  in
  let rec parse_sexplist acc =
    match%sedlex buf with
    | white_spaces, Opt ')', white_spaces, Opt '(', white_spaces ->
      parse_sexplist (parse_instruction buf :: acc)
    | ')', white_spaces, eof -> List.rev acc
    | _ -> raise (SyntaxError (lexeme_start buf))
  in
  match%sedlex buf with
  | "0x" -> parse_hex ~ignore_data_section:ignore_data_section buf
  | hexdigit -> rollback buf; parse_hex ~ignore_data_section:ignore_data_section buf
  | white_spaces, eof -> []
  | white_spaces, '[', white_spaces, ']', white_spaces, eof -> []
  | white_spaces, '[', white_spaces -> parse_ocamllist ([parse_instruction buf])
  | white_spaces, '(', white_spaces, ')', white_spaces, eof -> []
  | white_spaces, '(', white_spaces -> parse_sexplist ([])
  | white_spaces -> parse_wslist parse_pusharg buf
  | _ -> raise (SyntaxError (lexeme_start buf))

