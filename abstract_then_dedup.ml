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
open Ebso
open Instruction

module Snippet_mod = struct
  module T = struct
    type t = string [@@deriving sexp]
    let wsz = ref 0

    let set_wsz s = wsz := s

    let abstract_pusharg sp =
      Sedlexing.Latin1.from_string sp |> Parser.parse
      |> Program.val_to_const !wsz
      |> List.mapi ~f:(fun j i ->
          match i with PUSH (Const _) -> PUSH (Const (Int.to_string j)) | _ -> i)

    let equal sp1 sp2 =
      let p1 = abstract_pusharg sp1
      and p2 = abstract_pusharg sp2 in
      Program.equal p1 p2

    let compare sp1 sp2 =
      if equal sp1 sp2 then 0
      else
        let lc = Int.compare (String.length sp1) (String.length sp2) in
        if lc <> 0 then lc else String.compare sp1 sp2
  end

  include T
  include Comparable.Make(T)
end

let () =
  let open Command.Let_syntax in
  Command.basic ~summary:"First abstract PUSH arguments using given word size, then remove duplicate snippets"
    [%map_open
      let f = anon ("CSVFILE" %: string)
      and wordsize = flag "word-size" (required int)
          ~doc:"wsz word size, i.e., number of bits used for stack elements"
      and outfile = flag "outfile" (required string)
          ~doc:"f.csv save result to f.csv"
      in
      fun () ->
        Snippet_mod.set_wsz wordsize;
        let m = Map.empty (module Snippet_mod) in
        let c = Csv.Rows.load ~has_header:false f in
        let (header, data) = (Csv.Row.to_list (List.hd_exn c), List.tl_exn c) in
        let m =
          List.fold_left data ~init:m
            ~f:(fun m' r ->
                let (h, t) =  List.split_n (Csv.Row.to_list r) 1 in
                Map.update m' (List.hd_exn h)
                  ~f:(function | None -> (t, Z.one) | Some (d, n) -> (d, Z.succ n)))
        in
        let outcsv =
          List.map (Map.to_alist ~key_order:`Increasing m)
            ~f:(fun (k, (d, c)) -> [k] @ d @ [Z.to_string c])
        in
        Csv.save outfile ((header @ ["snippet count"]) :: outcsv)
    ]
  |> Command.run
