open Core
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

let () =
  let open Command.Let_syntax in
  Command.basic ~summary:"ebso: An EVM Bytecode Super Optimizer"
    [%map_open
      let file = flag "file" (optional string) ~doc:"f read input from file f"
      in
      fun () ->
        match file with
        | None -> super_optimize zero
        | Some f -> super_optimize f
    ]
  |> Command.run ~version:"0.1"

  (* let p' = super_optimize zero in *)
