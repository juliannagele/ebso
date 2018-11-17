open Core

let add_size = function
  | p :: rest ->
    let size =
      Sedlexing.Latin1.from_string p |> Parser.parse
      |> List.length |> Int.to_string
    in
    p :: size :: rest
  | [] -> failwith "empty row"

let () =
  let open Command.Let_syntax in
  Command.basic ~summary:"drop terminal instructions from csv"
    [%map_open
      let f = anon ("CSVFILE" %: string)
      and outfile = flag "outfile" (optional_with_default "withsize.csv" string)
          ~doc:"f.csv save result to f.csv"
      in
      fun () ->
        let c = Csv.Rows.load ~has_header:true f |> List.map ~f:Csv.Row.to_list in
        let c = List.map c ~f:add_size in
        Csv.save outfile (["input";"instruction count";"count";"optimized";"gas saved";"known optimal";"translation validation"] :: c)
    ]
  |> Command.run
