open Core

type stackarg =
  | Val of int [@printer fun fmt x -> fprintf fmt "%i" x]
  | Tmpl
[@@deriving show { with_path = false }, eq, sexp]

let stackarg_of_sexp s = match s with
  | Sexp.Atom i -> if String.equal i "Tmpl" then Tmpl else Val (Int.of_string i)
  | Sexp.List _ -> failwith "could not parse argument of PUSH"

let all_of_stackarg = [Tmpl]

type idx =
  | I [@value 1] | II | III | IV | V
  | VI | VII | VIII | IX | X
  | XI | XII | XIII | XIV | XV | XVI
[@@deriving show { with_path = false }, eq, enum, enumerate, sexp]

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
  | DUP of idx
  (* 90s:  Exchange Operations *)
  | SWAP of idx
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
[@@deriving show { with_path = false }, eq, enumerate, sexp]

(* list of instructions that are encodable, i.e., can be super optimized *)
let encodable = [
    ADD
  ; MUL
  ; POP
  ; SUB
] @ List.map all_of_stackarg ~f:(fun a -> PUSH a)
  @ List.map all_of_idx ~f:(fun i -> SWAP i)

let delta_alpha = function
  | ADD -> (2, 1)
  | MUL -> (2, 1)
  | PUSH _ -> (0, 1)
  | POP -> (1, 0)
  | SUB -> (2, 1)
  | SWAP i -> (idx_to_enum i + 1, idx_to_enum i + 1)
  | _ -> failwith "not implemented"

let gas_cost = function
  | ADD -> 3
  | MUL -> 5
  | PUSH _ -> 3
  | POP -> 2
  | SUB -> 3
  | SWAP _ -> 3
  | _ -> failwith "not implemented"
