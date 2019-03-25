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
open Program
open Evmenc

let ebso_snippet = function
  | Terminal (p, _) -> Some p
  | Next p -> Some p
  | _ -> None

let show_ebso_snippet s =
  let ea = mk_enc_consts s `All in
  [ Program.show_hex s
  ; Program.show_h s
  ; [%show: int] (List.length s)
  ; [%show: int] (List.length ea.xs)
  ; [%show: int] (List.length (List.concat (Map.data ea.uis)))
  ; [%show: int] (List.length ea.ss)
  ]

let create_ebso_snippets bbs =
  [ "byte code"
  ; "op code"
  ; "instruction count"
  ; "stack depth"
  ; "uninterpreted count"
  ; "storage access count"
  ] ::
  List.filter_map bbs ~f:(fun bb -> ebso_snippet bb |> Option.map ~f:(show_ebso_snippet))
