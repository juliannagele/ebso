open Evmenc

let zero = [
  PUSH 42;
  PUSH 21;
  PUSH 0;
  SUB;
  ADD;
]

let zero_optzd = [
  PUSH 21;
  PUSH 42;
  SUB;
]

(* Goal: super_optimze zero == zero_optzd *)

let () = ()
  (* let p' = super_optimize zero in *)
