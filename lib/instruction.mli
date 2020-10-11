(*   Copyright 2020 Julian Nagele and Maria A Schett

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
  | I | II | III | IV | V
  | VI | VII | VIII | IX | X
  | XI | XII | XIII | XIV | XV | XVI

val pp_idx : Format.formatter -> idx -> unit

val show_idx : idx -> string

val equal_idx : idx -> idx -> bool

val min_idx : int

val max_idx : int

val idx_to_enum : idx -> int

val idx_of_enum : int -> idx option

val all_of_idx : idx list

val idx_of_sexp : Sexp.t -> idx

val sexp_of_idx : idx -> Sexp.t

val compare_idx : idx -> idx -> int

val show_idx_hex : idx -> string

module T : sig
  type t  =
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
    | PUSH of Pusharg.t
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
end

type t = T.t

val pp : Format.formatter -> t -> unit

val show : t -> string

val equal : t -> t -> bool

val all : t list

val t_of_sexp : Sexp.t -> t

val sexp_of_t : t -> Sexp.t

val compare : t -> t -> int

val delta_alpha : t -> int * int

val arity : t -> int

val is_const : t -> bool

val unint_name : int -> t -> string

val unint_rom_name : t -> string

val uninterpreted : t list

val is_uninterpreted : t -> bool

val constant_uninterpreted : t list

val outsideeffect : t list

val encodable : t list

val gas_cost : t -> Gas_cost.t

val show_hex : t -> string

module Map : sig
  type 'a t
  val empty : 'a t
  val update : 'a t -> T.t -> f:('a option -> 'a) -> 'a t
  val keys : 'a t ->  T.t list
  val data : 'a t -> 'a list
  val find_exn : 'a t -> T.t -> 'a
  val find : 'a t -> T.t -> 'a option
  val fold : 'a t -> init:'b -> f:(key:T.t -> data:'a -> 'b -> 'b) -> 'b
  val merge : 'a t -> 'b t -> f:(key:T.t -> [ `Both of 'a * 'b | `Left of 'a | `Right of 'b ] -> 'c option) -> 'c t
end
