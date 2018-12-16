(*   Copyright 2018 Julian Nagele and Maria A Schett

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
