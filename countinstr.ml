open Core

let count_from_program m p =
  let up = function
    | None -> Z.one
    | Some n -> Z.succ n
  in
  List.fold p ~init:m ~f:(fun m' i -> Map.update m' i ~f:up)

let count_from_filepath m f =
  let ic = In_channel.create f in
  let buf = Sedlexing.Latin1.from_channel ic in
  let p =
    try Parser.parse_hex buf
    with Parser.SyntaxError i ->
      print_string (f ^ ", " ^ Int.to_string i ^ "\n");
      Out_channel.flush Out_channel.stdout; []
  in
  In_channel.close ic;
  count_from_program m p

let show_instr = function
  | Instruction.PUSH _ -> "PUSH"
  | i -> [%show: Instruction.t] i

let () =
  let module M = Map.Make_plain (Instruction) in
  let m = M.empty in
  let open Command.Let_syntax in
  Command.basic ~summary:"count-instr: count instructions in bytecode"
    [%map_open
      let fns = anon ("FILENAMES" %: string) in
      fun () ->
        let fs = In_channel.read_lines fns in
        let m' = List.fold fs ~init:m ~f:count_from_filepath in
        print_string "Instruction,Count\n";
        Map.iteri m' ~f:(fun ~key:k ~data:d ->
            print_string (show_instr k ^ "," ^ (Z.to_string d) ^ "\n"))
    ]
  |> Command.run
