open Core
open Evmenc

let p0 = [
  PUSH (Val 1);
  PUSH (Val 1);
  ADD;
]

let () =
  let open Command.Let_syntax in
  Command.basic ~summary:"ebso: An EVM Bytecode Super Optimizer"
    [%map_open
      let file = flag "file" (optional string) ~doc:"f read input from file f"
      in
      fun () ->
        match file with
        | None -> print_string @@ super_optimize p0 [PUSH Tmpl; ADD; SUB]
        | Some _ -> print_string @@ super_optimize p0 []
    ]
  |> Command.run ~version:"0.1"
