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
