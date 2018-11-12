open Core
open Instruction

let abstract_pusharg wsz sp =
  Sedlexing.Latin1.from_string sp |> Parser.parse
  |> Program.val_to_const wsz
  |> List.mapi ~f:(fun j i ->
      match i with PUSH (Const _) -> PUSH (Const (Int.to_string j)) | _ -> i)

let equal_mod_pusharg wsz sp1 sp2 =
  let p1 = abstract_pusharg wsz sp1
  and p2 = abstract_pusharg wsz sp2 in
  Program.equal p1 p2

let compare_prog wsz sp1 sp2 =
  if equal_mod_pusharg wsz sp1 sp2 then 0
  else
    let lc = Int.compare (String.length sp1) (String.length sp2) in
    if lc <> 0 then lc else String.compare sp1 sp2

let () =
  let open Command.Let_syntax in
  Command.basic ~summary:"sample snippets from csv"
    [%map_open
      let f = anon ("CSVFILE" %: string)
      and wordsize = flag "word-size" (required int)
          ~doc:"wsz word size, i.e., number of bits used for stack elements"
      in
      fun () ->
        let c = Csv.Rows.load ~has_header:true f |> List.map ~f:Csv.Row.to_list in
        let ps = List.map c ~f:List.hd_exn in
        let ps = List.dedup_and_sort ~compare:(compare_prog wordsize) ps in
        List.iter ps ~f:(print_endline)
    ]
  |> Command.run
