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
  let rec parse_token acc =
    match%sedlex buf with
    | white_space -> parse_token acc
    | "STOP" -> parse_token (STOP :: acc)
    | "ADD" -> parse_token (ADD :: acc)
    | "MUL" -> parse_token (MUL :: acc)
    | "SUB" -> parse_token (SUB :: acc)
    | "DIV" -> parse_token (DIV :: acc)
    | "SDIV" -> parse_token (SDIV :: acc)
    | "MOD" -> parse_token (MOD :: acc)
    | "SMOD" -> parse_token (SMOD :: acc)
    | "ADDMOD" -> parse_token (ADDMOD :: acc)
    | "MULMOD" -> parse_token (MULMOD :: acc)
    | "EXP" -> parse_token (EXP :: acc)
    | "SIGNEXTEND" -> parse_token (SIGNEXTEND :: acc)
    | "LT" -> parse_token (LT :: acc)
    | "GT" -> parse_token (GT :: acc)
    | "SLT" -> parse_token (SLT :: acc)
    | "SGT" -> parse_token (SGT :: acc)
    | "EQ" -> parse_token (EQ :: acc)
    | "ISZERO" -> parse_token (ISZERO :: acc)
    | "AND" -> parse_token (AND :: acc)
    | "OR" -> parse_token (OR :: acc)
    | "XOR" -> parse_token (XOR :: acc)
    | "NOT" -> parse_token (NOT :: acc)
    | "BYTE" -> parse_token (BYTE :: acc)
    | "SHL" -> parse_token (SHL :: acc)
    | "SHR" -> parse_token (SHR :: acc)
    | "SAR" -> parse_token (SAR :: acc)
    | "SHA3" -> parse_token (SHA3 :: acc)
    | "ADDRESS" -> parse_token (ADDRESS :: acc)
    | "BALANCE" -> parse_token (BALANCE :: acc)
    | "ORIGIN" -> parse_token (ORIGIN :: acc)
    | "CALLER" -> parse_token (CALLER :: acc)
    | "CALLVALUE" -> parse_token (CALLVALUE :: acc)
    | "CALLDATALOAD" -> parse_token (CALLDATALOAD :: acc)
    | "CALLDATASIZE" -> parse_token (CALLDATASIZE :: acc)
    | "CALLDATACOPY" -> parse_token (CALLDATACOPY :: acc)
    | "CODESIZE" -> parse_token (CODESIZE :: acc)
    | "CODECOPY" -> parse_token (CODECOPY :: acc)
    | "GASPRICE" -> parse_token (GASPRICE :: acc)
    | "EXTCODESIZE" -> parse_token (EXTCODESIZE :: acc)
    | "EXTCODECOPY" -> parse_token (EXTCODECOPY :: acc)
    | "RETURNDATASIZE" -> parse_token (RETURNDATASIZE :: acc)
    | "RETURNDATACOPY" -> parse_token (RETURNDATACOPY :: acc)
    | "EXTCODEHASH" -> parse_token (EXTCODEHASH :: acc)
    | "BLOCKHASH" -> parse_token (BLOCKHASH :: acc)
    | "COINBASE" -> parse_token (COINBASE :: acc)
    | "TIMESTAMP" -> parse_token (TIMESTAMP :: acc)
    | "NUMBER" -> parse_token (NUMBER :: acc)
    | "DIFFICULTY" -> parse_token (DIFFICULTY :: acc)
    | "GASLIMIT" -> parse_token (GASLIMIT :: acc)
    | "POP" -> parse_token (POP :: acc)
    | "MLOAD" -> parse_token (MLOAD :: acc)
    | "MSTORE" -> parse_token (MSTORE :: acc)
    | "MSTORE8" -> parse_token (MSTORE8 :: acc)
    | "SLOAD" -> parse_token (SLOAD :: acc)
    | "SSTORE" -> parse_token (SSTORE :: acc)
    | "JUMP" -> parse_token (JUMP :: acc)
    | "JUMPI" -> parse_token (JUMPI :: acc)
    | "PC" -> parse_token (PC :: acc)
    | "MSIZE" -> parse_token (MSIZE :: acc)
    | "GAS" -> parse_token (GAS :: acc)
    | "JUMPDEST" -> parse_token (JUMPDEST :: acc)
    | "PUSH", Opt re32 -> parse_stackarg acc
    | "DUP", re16 ->
      let idx = parse_idx "DUP" (Latin1.lexeme buf) in
      parse_token (DUP idx :: acc)
    | "SWAP", re16 ->
      let idx = parse_idx "SWAP" (Latin1.lexeme buf) in
      parse_token (SWAP idx :: acc)
    | "LOG0" -> parse_token (LOG0 :: acc)
    | "LOG1" -> parse_token (LOG1 :: acc)
    | "LOG2" -> parse_token (LOG2 :: acc)
    | "LOG3" -> parse_token (LOG3 :: acc)
    | "LOG4" -> parse_token (LOG4 :: acc)
    | "JUMPTO" -> parse_token (JUMPTO :: acc)
    | "JUMPIF" -> parse_token (JUMPIF :: acc)
    | "JUMPV" -> parse_token (JUMPV :: acc)
    | "JUMPSUB" -> parse_token (JUMPSUB :: acc)
    | "JUMPSUBV" -> parse_token (JUMPSUBV :: acc)
    | "BEGINSUB" -> parse_token (BEGINSUB :: acc)
    | "BEGINDATA" -> parse_token (BEGINDATA :: acc)
    | "RETURNSUB" -> parse_token (RETURNSUB :: acc)
    | "PUTLOCAL" -> parse_token (PUTLOCAL :: acc)
    | "GETLOCAL" -> parse_token (GETLOCAL :: acc)
    | "CREATE" -> parse_token (CREATE :: acc)
    | "CALL" -> parse_token (CALL :: acc)
    | "CALLCODE" -> parse_token (CALLCODE :: acc)
    | "RETURN" -> parse_token (RETURN :: acc)
    | "DELEGATECALL" -> parse_token (DELEGATECALL :: acc)
    | "CREATE2" -> parse_token (CREATE2 :: acc)
    | "STATICCALL" -> parse_token (STATICCALL :: acc)
    | "REVERT" -> parse_token (REVERT :: acc)
    | "INVALID" -> parse_token (INVALID :: acc)
    | "SELFDESTRUCT" -> parse_token (SELFDESTRUCT :: acc)
    | eof -> acc
    | _ -> raise (SyntaxError (lexeme_start buf))
  and parse_stackarg acc =
    match%sedlex buf with
    | white_space -> parse_stackarg acc
    | "Tmpl" -> parse_token (PUSH Tmpl :: acc)
    | "0x", Plus hexdigit | Plus digit ->
      let i = Int.of_string @@ Latin1.lexeme buf in
      parse_token (PUSH (Val i) :: acc)
    | _ -> raise (SyntaxError (lexeme_start buf))
  in
  parse_token [] |> List.rev

let parse_hex_idx s n =
  let idxo = idx_of_enum @@ Int.of_string ("0x" ^ s) - n in
  Option.value_exn ~message:("parse hex index failed") idxo

let parse_hex_bytes n buf =
  let rec parse_hex_bytes n acc =
    if n <= 0 then acc
    else
      match%sedlex buf with
      | Rep (hexdigit, 2) -> parse_hex_bytes (n - 1) (acc ^ Latin1.lexeme buf)
      | _ -> raise (SyntaxError (lexeme_start buf))
  in
  Int.of_string @@ parse_hex_bytes n "0x"

let parse_hex buf =
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
      (* 0x60 = 96, so x in PUSHx is 0x<lexeme> - 95 *)
      let n = Int.of_string ("0x" ^ Latin1.lexeme buf) - 95 in
      let i = parse_hex_bytes n buf in
      parse_token (PUSH (Val i) :: acc)
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
    | eof -> acc
    | _ -> raise (SyntaxError (lexeme_start buf))
  in
  parse_token [] |> List.rev
