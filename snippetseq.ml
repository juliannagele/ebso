open Core
open Instruction

let canonicalize_const_names p =
  List.mapi p ~f:(fun j i ->
      match i with PUSH (Const _) -> PUSH (Const (Int.to_string j)) | _ -> i)

let () =
  let open Command.Let_syntax in
  Command.basic ~summary:"check whether two snippets are equal after replacing \
                          PUSH arguments that do not fit in word-size bits by \
                          variables"
    [%map_open
      let s1 = anon ("SNIPPET1" %: string)
      and s2 = anon ("SNIPPET2" %: string)
      and wordsize = flag "word-size" (required int)
          ~doc:"wsz word size, i.e., number of bits used for stack elements"
      in
      fun () ->
        let p1 =
          Sedlexing.Latin1.from_string s1 |> Parser.parse
          |> Program.val_to_const wordsize |> canonicalize_const_names
        and p2 =
          Sedlexing.Latin1.from_string s2 |> Parser.parse
          |> Program.val_to_const wordsize |> canonicalize_const_names
        in
        print_endline @@ Bool.to_string (Program.equal p1 p2)
    ]
  |> Command.run
