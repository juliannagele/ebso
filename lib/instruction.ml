open Core

let num_string_to_dec x = Z.of_string x |> Z.to_string

type stackarg =
  (* string either in hexadecimal format starting with 0x or in decimal format *)
  | Val of string [@printer fun fmt x -> fprintf fmt "%s" (num_string_to_dec x)]
  | Tmpl
[@@deriving show { with_path = false }, sexp, compare]

let equal_stackarg x y = match (x, y) with
  | Val x, Val y -> Z.equal (Z.of_string x) (Z.of_string y)
  | Tmpl, Tmpl -> true
  | _, _ -> false

let stackarg_of_sexp s = match s with
  | Sexp.Atom i -> if String.equal i "Tmpl" then Tmpl else Val i
  | Sexp.List _ -> failwith "could not parse argument of PUSH"

let all_of_stackarg = [Tmpl]

type idx =
  | I [@value 1] | II | III | IV | V
  | VI | VII | VIII | IX | X
  | XI | XII | XIII | XIV | XV | XVI
[@@deriving show { with_path = false }, eq, enum, enumerate, sexp, compare]

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

(* list of instructions that are encodable, i.e., can be super optimized *)
let encodable = [
    ADD
  ; MUL
  ; SUB
  ; DIV
  ; MOD
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
  | MOD -> (2, 1)
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
  | MOD -> 5
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
