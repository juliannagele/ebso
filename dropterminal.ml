open Core

let drop_terminal sp =
  let bbs =
    Sedlexing.Latin1.from_string sp |> Parser.parse
    |> Program.split_into_bbs
  in
  match bbs with
  | [Terminal (p, _)] -> Program.show_hex p
  | [Next p] -> Program.show_hex p
  | [NotEncodable p] -> Program.show_hex p
  | _ -> failwith "multiple bbs"

let () =
  let open Command.Let_syntax in
  Command.basic ~summary:"drop terminal instructions from csv"
    [%map_open
      let f = anon ("CSVFILE" %: string)
      and outfile = flag "outfile" (optional_with_default "sorted_nt.csv" string)
          ~doc:"f.csv save result to f.csv"
      in
      fun () ->
        let c = Csv.Rows.load ~has_header:false f |> List.map ~f:Csv.Row.to_list in
        let c = List.map c ~f:(function [p; c] -> [drop_terminal p; c] | _ -> failwith "wrong format") in
        Csv.save outfile (["input"; "count"] :: c)
    ]
  |> Command.run
