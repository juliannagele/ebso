open Core
open Stackarg

type idx =
  | I [@value 1] | II | III | IV | V
  | VI | VII | VIII | IX | X
  | XI | XII | XIII | XIV | XV | XVI
[@@deriving show { with_path = false }, eq, enum, enumerate, sexp, compare]

let show_idx_hex idx = Z.format "x" (Z.of_int (idx_to_enum idx - 1))

type t =
  (* 0s:  Stop and Arithmetic Operations *)
  | STOP | ADD | MUL | SUB | DIV | SDIV | MOD | SMOD | ADDMOD | MULMOD | EXP
  | SIGNEXTEND
  (* 10s:  Comparison & Bitwise Logic Operations *)
  | LT | GT | SLT | SGT | EQ | ISZERO | AND | OR | XOR | NOT | BYTE
  (* EIP 145 *)
  | SHL | SHR | SAR
  (* 20s:  SHA3 *)
  | SHA3
  (* 30s:  Environmental Information *)
  | ADDRESS | BALANCE | ORIGIN | CALLER | CALLVALUE | CALLDATALOAD | CALLDATASIZE
  | CALLDATACOPY | CODESIZE | CODECOPY | GASPRICE | EXTCODESIZE | EXTCODECOPY
  | RETURNDATASIZE | RETURNDATACOPY
  (* EIP 1052 *)
  | EXTCODEHASH
  (* 40s:  Block Information *)
  | BLOCKHASH | COINBASE | TIMESTAMP | NUMBER | DIFFICULTY | GASLIMIT
  (* 50s:  Stack, Memory, Storage and Flow Operations *)
  | POP | MLOAD | MSTORE | MSTORE8 | SLOAD | SSTORE | JUMP | JUMPI | PC | MSIZE
  | GAS | JUMPDEST
  (* 60s & 70s:  Push Operations *)
  | PUSH of stackarg [@printer fun fmt x -> fprintf fmt "PUSH %s" (show_stackarg x)]
  (* 80s:  Duplication Operations *)
  | DUP of idx [@printer fun fmt i -> fprintf fmt "DUP%i" (idx_to_enum i)]
  (* 90s:  Exchange Operations *)
  | SWAP of idx [@printer fun fmt i -> fprintf fmt "SWAP%i" (idx_to_enum i)]
  (* a0s:  Logging Operations *)
  | LOG0 | LOG1 | LOG2 | LOG3 | LOG4
  (* b0s: EIP 615 *)
  | JUMPTO | JUMPIF | JUMPV | JUMPSUB | JUMPSUBV | BEGINSUB | BEGINDATA
  | RETURNSUB | PUTLOCAL | GETLOCAL
  (* f0s:  System operations *)
  | CREATE | CALL | CALLCODE | RETURN | DELEGATECALL
  (* EIP 1014 *)
  | CREATE2
  | STATICCALL | REVERT | INVALID | SELFDESTRUCT
[@@deriving show {with_path = false}, eq, enumerate, sexp, compare]

let compare i i2 = match (i, i2) with
  | (PUSH _, PUSH _) -> 0
  | _ -> [%compare: t] i i2

let mod_to_ses ses = function
  | PUSH x -> PUSH (mod_stackarg_to_ses ses x)
  | i -> i

let val_to_const ses instr =
  let max_repr = Z.pow (Z.of_int 2) ses in
  match instr with
  | PUSH (Val x) ->
    let v = if Z.of_string x >= max_repr then Const (from_valarg x) else Val x in
    PUSH v
  | i -> i

let const_to_val = function
  | PUSH (Const c) -> PUSH (Val (to_valarg c))
  | i -> i

(* list of instructions that are encodable, i.e., can be super optimized *)
let encodable = [
    ADD
  ; MUL
  ; SUB
  ; DIV
  ; SDIV
  ; MOD
  ; SMOD
  ; ADDMOD
  ; MULMOD
  ; LT
  ; GT
  ; SLT
  ; SGT
  ; EQ
  ; ISZERO
  ; AND
  ; OR
  ; XOR
  ; NOT
  ; POP
] @ List.map all_of_stackarg ~f:(fun a -> PUSH a)
  @ List.map all_of_idx ~f:(fun i -> SWAP i)
  @ List.map all_of_idx ~f:(fun i -> DUP i)

let delta_alpha = function
  | ADD -> (2, 1)
  | MUL -> (2, 1)
  | SUB -> (2, 1)
  | DIV -> (2, 1)
  | SDIV -> (2, 1)
  | MOD -> (2, 1)
  | SMOD -> (2, 1)
  | ADDMOD -> (3, 1)
  | MULMOD -> (3, 1)
  | LT -> (2, 1)
  | GT -> (2, 1)
  | SLT -> (2, 1)
  | SGT -> (2, 1)
  | EQ -> (2, 1)
  | ISZERO -> (1, 1)
  | AND -> (2, 1)
  | OR -> (2, 1)
  | XOR -> (2, 1)
  | NOT -> (1, 1)
  | PUSH _ -> (0, 1)
  | POP -> (1, 0)
  | SWAP i -> (idx_to_enum i + 1, idx_to_enum i + 1)
  | DUP i -> (idx_to_enum i, idx_to_enum i + 1)
  | _ -> failwith "not implemented"

let gas_cost = function
  | ADD -> 3
  | MUL -> 5
  | SUB -> 3
  | DIV -> 5
  | SDIV -> 5
  | MOD -> 5
  | SMOD -> 5
  | ADDMOD -> 8
  | MULMOD -> 8
  | LT -> 3
  | GT -> 3
  | SLT -> 3
  | SGT -> 3
  | EQ -> 3
  | ISZERO -> 3
  | AND -> 3
  | OR -> 3
  | XOR -> 3
  | NOT -> 3
  | PUSH _ -> 3
  | POP -> 2
  | SWAP _ -> 3
  | DUP _ -> 3
  | _ -> failwith "not implemented"

let show_hex = function
  | STOP -> "00"
  | ADD -> "01"
  | MUL -> "02"
  | SUB -> "03"
  | DIV -> "04"
  | SDIV -> "05"
  | MOD -> "06"
  | SMOD -> "07"
  | ADDMOD -> "08"
  | MULMOD -> "09"
  | EXP -> "0a"
  | SIGNEXTEND -> "0b"
  | LT -> "10"
  | GT -> "11"
  | SLT -> "12"
  | SGT -> "13"
  | EQ -> "14"
  | ISZERO -> "15"
  | AND -> "16"
  | OR -> "17"
  | XOR -> "18"
  | NOT -> "19"
  | BYTE -> "1a"
  | SHL -> "1b"
  | SHR -> "1c"
  | SAR -> "1d"
  | SHA3 -> "20"
  | ADDRESS -> "30"
  | BALANCE -> "31"
  | ORIGIN -> "32"
  | CALLER -> "33"
  | CALLVALUE -> "34"
  | CALLDATALOAD -> "35"
  | CALLDATASIZE -> "36"
  | CALLDATACOPY -> "37"
  | CODESIZE -> "38"
  | CODECOPY -> "39"
  | GASPRICE -> "3a"
  | EXTCODESIZE -> "3b"
  | EXTCODECOPY -> "3c"
  | RETURNDATASIZE -> "3d"
  | RETURNDATACOPY -> "3e"
  | EXTCODEHASH -> "3f"
  | BLOCKHASH -> "40"
  | COINBASE -> "41"
  | TIMESTAMP -> "42"
  | NUMBER -> "43"
  | DIFFICULTY -> "44"
  | GASLIMIT -> "45"
  | POP -> "50"
  | MLOAD -> "51"
  | MSTORE -> "52"
  | MSTORE8 -> "53"
  | SLOAD -> "54"
  | SSTORE -> "55"
  | JUMP -> "56"
  | JUMPI -> "57"
  | PC -> "58"
  | MSIZE -> "59"
  | GAS -> "5a"
  | JUMPDEST -> "5b"
  | PUSH x ->
    let hx = show_stackarg_hex x in
    (* 96 = 0x60, so 95 + number of bytes is the bytecode we need *)
    Z.format "x" (Z.of_int (95 + (String.length hx / 2))) ^ hx
  | DUP idx -> "8" ^ show_idx_hex idx
  | SWAP idx -> "9" ^ show_idx_hex idx
  | LOG0 -> "a0"
  | LOG1 -> "a1"
  | LOG2 -> "a2"
  | LOG3 -> "a3"
  | LOG4 -> "a4"
  | JUMPTO -> "b0"
  | JUMPIF -> "b1"
  | JUMPV -> "b2"
  | JUMPSUB -> "b3"
  | JUMPSUBV -> "b4"
  | BEGINSUB -> "b5"
  | BEGINDATA -> "b6"
  | RETURNSUB -> "b7"
  | PUTLOCAL -> "b8"
  | GETLOCAL -> "b9"
  | CREATE -> "f0"
  | CALL -> "f1"
  | CALLCODE -> "f2"
  | RETURN -> "f3"
  | DELEGATECALL -> "f4"
  | CREATE2 -> "f5"
  | STATICCALL -> "fa"
  | REVERT -> "fd"
  | INVALID -> "fe"
  | SELFDESTRUCT -> "ff"
