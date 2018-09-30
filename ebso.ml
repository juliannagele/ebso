open Core
open Evmenc

let p0 = [
  PUSH (Val 1);
  PUSH (Val 1);
  ADD;
]

let p0_optzd = [
  PUSH (Val 2);
]

(* Goal 1: super_optimze p0 == p0_optzd *)

let zero = [
  PUSH (Val 42);
  PUSH (Val 21);
  PUSH (Val 0);
  SUB;
  ADD;
]

let zero_optzd = [
  PUSH (Val 21);
  PUSH (Val 42);
  SUB;
]

(* Goal 2: super_optimze zero == zero_optzd *)

let () =
  let open Command.Let_syntax in
  Command.basic ~summary:"ebso: An EVM Bytecode Super Optimizer"
    [%map_open
      let file = flag "file" (optional string) ~doc:"f read input from file f"
      in
      fun () ->
        match file with
        | None -> print_string @@ super_optimize p0 [PUSH (Val 2); PUSH (Val 1); ADD]
        | Some _ -> print_string @@ super_optimize p0 []
    ]
  |> Command.run ~version:"0.1"

  (* let p' = super_optimize zero in *)
