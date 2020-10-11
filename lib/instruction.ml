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

type idx =
  | I [@value 1] | II | III | IV | V
  | VI | VII | VIII | IX | X
  | XI | XII | XIII | XIV | XV | XVI
[@@deriving show { with_path = false }, eq, enum, enumerate, sexp, compare]

let show_idx_hex idx = Z.format "x" (Z.of_int (idx_to_enum idx - 1))

module T = struct
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
    | PUSH of Pusharg.t [@printer fun fmt x -> fprintf fmt "PUSH %s" (Pusharg.show x)]
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
end

include T

module Map = Map.Make(T)

let delta_alpha = function
  | STOP -> (0, 0)
  | ADD -> (2, 1)
  | MUL -> (2, 1)
  | SUB -> (2, 1)
  | DIV -> (2, 1)
  | SDIV -> (2, 1)
  | MOD -> (2, 1)
  | SMOD -> (2, 1)
  | ADDMOD -> (3, 1)
  | MULMOD -> (3, 1)
  | EXP -> (2, 1)
  | SIGNEXTEND -> (2, 1)
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
  | BYTE -> (2, 1)
  | SHL -> (2, 1)
  | SHR -> (2, 1)
  | SAR -> (2, 1)
  | SHA3 -> (2, 1)
  | ADDRESS -> (0, 1)
  | BALANCE -> (1, 1)
  | ORIGIN -> (0, 1)
  | CALLER -> (0, 1)
  | CALLVALUE -> (0, 1)
  | CALLDATALOAD -> (1, 1)
  | CALLDATASIZE -> (0, 1)
  | CALLDATACOPY -> (3, 0)
  | CODESIZE -> (0, 1)
  | GASPRICE -> (0, 1)
  | EXTCODESIZE -> (1, 1)
  | RETURNDATASIZE -> (0, 1)
  | RETURNDATACOPY -> (3, 0)
  | BLOCKHASH -> (1, 1)
  | COINBASE -> (0, 1)
  | TIMESTAMP -> (0, 1)
  | NUMBER -> (0, 1)
  | DIFFICULTY -> (0, 1)
  | GASLIMIT -> (0, 1)
  | POP -> (1, 0)
  | MLOAD -> (1, 1)
  | MSTORE -> (2, 0)
  | MSTORE8 -> (2, 0)
  | SLOAD -> (1, 1)
  | SSTORE -> (2, 0)
  | JUMP -> (1, 0)
  | JUMPI -> (2, 0)
  | PC -> (0, 1)
  | MSIZE -> (0, 1)
  | GAS -> (0, 1)
  | JUMPDEST -> (0, 0)
  | PUSH _ -> (0, 1)
  | DUP i -> (idx_to_enum i, idx_to_enum i + 1)
  | SWAP i -> (idx_to_enum i + 1, idx_to_enum i + 1)
  | LOG0 -> (2, 0)
  | LOG1 -> (3, 0)
  | LOG2 -> (4, 0)
  | LOG3 -> (5, 0)
  | LOG4 -> (6, 0)
  | CREATE -> (3, 1)
  | CALL -> (7, 1)
  | CALLCODE -> (7, 1)
  | RETURN -> (2, 0)
  | DELEGATECALL -> (6, 1)
  | STATICCALL -> (6, 1)
  | REVERT -> (2, 0)
  | SELFDESTRUCT -> (1, 0)
  | INVALID -> (-1, -1) (* hacky quick fix *)
  | i -> failwith ("delta_alpha not implemented for " ^ show i)

let arity i = delta_alpha i |> Tuple.T2.get1

let is_const i = arity i = 0

(* names of variables for representing an uninterpreted instruction
   constant uninterpreted instructions have only one variable,
   uninterpreted instructions with arguments need one variable per use
*)
let unint_name j i =
  let suff = if is_const i then "" else "_" ^ Int.to_string j in
  "x_" ^ show i ^ suff

let unint_rom_name i =
  "f_" ^ show i

(* list of instructions that remain uninterpreted *)
let uninterpreted = [
    EXP
  ; SIGNEXTEND
  ; BYTE
  ; SHA3
  ; ADDRESS
  ; BALANCE
  ; ORIGIN
  ; CALLER
  ; CALLVALUE
  ; CALLDATALOAD
  ; CALLDATASIZE
  ; CODESIZE
  ; GASPRICE
  ; EXTCODESIZE
  ; RETURNDATASIZE
  ; BLOCKHASH
  ; COINBASE
  ; TIMESTAMP
  ; NUMBER
  ; DIFFICULTY
  ; GASLIMIT
  ; MLOAD
  ; PC
  ; MSIZE
  ; GAS
  ]

let is_uninterpreted i = List.mem uninterpreted i ~equal:[%eq: t]

(* uninterpreted instructions that do not consume words from the stack *)
let constant_uninterpreted = List.filter uninterpreted ~f:is_const

(* list of instructions that have an effect on the outside world that is
   not encodable, i.e., effects on memory and logs *)
let outsideeffect = [
    CALLDATACOPY
  ; CODECOPY
  ; EXTCODECOPY
  ; RETURNDATACOPY
  ; MSTORE
  ; MSTORE8
  ; LOG0
  ; LOG1
  ; LOG2
  ; LOG3
  ; LOG4
  ]

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
  ; SLOAD
  ; SSTORE
] @ List.map Pusharg.all ~f:(fun a -> PUSH a)
  @ List.map all_of_idx ~f:(fun i -> SWAP i)
  @ List.map all_of_idx ~f:(fun i -> DUP i)

let gas_cost i =
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
    (* gas price of EXP depends on word on stack, 10 is lower bound,
       since EXP is uninterpreted only value relative to DUP matters *)
    | EXP -> 10
    | SIGNEXTEND -> 5
    | BYTE -> 3
    (* gas price of SHA3 depends on word on stack, 30 is lower bound,
       since SHA3 is uninterpreted only value relative to DUP matters *)
    | SHA3 -> 30
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
    | ADDRESS -> 2
    | BALANCE -> 400
    | ORIGIN -> 2
    | CALLER -> 2
    | CALLVALUE -> 2
    | CALLDATALOAD -> 3
    | CALLDATASIZE -> 2
    | CODESIZE -> 2
    | GASPRICE -> 2
    | EXTCODESIZE -> 700
    | RETURNDATASIZE -> 2
    | BLOCKHASH -> 20
    | COINBASE -> 2
    | TIMESTAMP -> 2
    | NUMBER -> 2
    | DIFFICULTY -> 2
    | GASLIMIT -> 2
    | POP -> 2
    | MLOAD -> 3
    | SLOAD -> 200
    (* fix to 20000 as upper bound *)
    | SSTORE -> 20000
    | PC -> 2
    | MSIZE -> 2
    | GAS -> 2
    | PUSH _ -> 3
    | SWAP _ -> 3
    | DUP _ -> 3
    | SHL | SHR | SAR -> 3
    | MSTORE -> 3
    | MSTORE8 -> 3
    | JUMPI -> 10
    | JUMP -> 8
    | JUMPDEST -> 1
    | JUMPV | JUMPSUBV -> 8
    | JUMPSUB | JUMPIF -> 5
    | JUMPTO -> 3
    | BEGINSUB | BEGINDATA | RETURNSUB | PUTLOCAL | GETLOCAL -> 3
    | STOP -> 0
    | INVALID -> 0
    | RETURN -> 0
    | REVERT -> 0
    | CALL | CALLCODE | DELEGATECALL | STATICCALL -> 700
    (* lower bound *)
    | CODECOPY | CALLDATACOPY | RETURNDATACOPY -> 3
    | EXTCODECOPY -> 700
    | SELFDESTRUCT -> 5000
    | CREATE | CREATE2 -> 32000
    (* lower bound *)
    | LOG0 | LOG1 | LOG2 | LOG3 | LOG4 -> 375
    | EXTCODEHASH -> 400
  in
  Gas_cost.of_int (gas_cost i)

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
    let hx = Pusharg.show_hex x in
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
