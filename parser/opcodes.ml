(* type of opcodes *)

type stack_arg = string

type t =
  | ADD
  | AND
  | CALLDATALOAD
  | CALLDATASIZE
  | CALLVALUE
  | CODECOPY
  | DIV
  | DUP1
  | DUP2
  | DUP3
  | DUP4
  | DUP15
  | EQ
  | GAS
  | ISZERO
  | INVALID
  | JUMP
  | JUMPI
  | JUMPDEST
  | LOG1
  | LT
  | KECCAK256
  | MLOAD
  | MSTORE
  | POP
  | PUSH1  of stack_arg
  | PUSH2  of stack_arg
  | PUSH3  of stack_arg
  | PUSH4  of stack_arg
  | PUSH6  of stack_arg
  | PUSH11 of stack_arg
  | PUSH24 of stack_arg
  | PUSH29 of stack_arg
  | RETURN
  | REVERT
  | SELFDESTRUCT
  | SIGNEXTEND
  | STOP
  | SUB
  | SWAP1
  | SWAP3
  | SWAP5
  | SWAP7
