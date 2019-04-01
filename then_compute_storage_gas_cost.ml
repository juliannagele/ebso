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
open Z3util
open Program
open Evmenc

let rec all_zero_nonzero_instantiations = function
  | [] -> [[]]
  | _ :: vs ->
    List.concat_map (all_zero_nonzero_instantiations vs)
      ~f:(fun vs -> [senum 3 :: vs; senum 0 :: vs])

let find_min_gas ea sp tp sts stt m =
  let all_vs = all_zero_nonzero_instantiations (forall_vars ea) in
  let rec find_min sg tg vss = match vss with
    | [] -> (sg, tg)
    | vs :: vss' ->
      Out_channel.prerr_endline ([%show: int] (List.length vss) ^ " instantiations left");
      let sg' = eval_gas ~xs:vs sts m (List.length sp)
      and tg' = eval_gas ~xs:vs stt m (List.length tp) in
      if sg' - tg' < sg - tg then find_min sg' tg' vss'
      else find_min sg tg vss'
  in
  find_min (total_gas_cost sp) (total_gas_cost tp) all_vs

let compute_gas sp tp =
  let open Z3Ops in
  let ea = mk_enc_consts sp (`User []) in
  let sts = mk_state ea "_s" in
  let stt = mk_state ea "_t" in
  let c = foralls (forall_vars ea)
      ((List.foldi tp ~init:(enc_program ea sts)
          ~f:(fun j enc oc -> enc <&> enc_instruction ea stt (num j) oc)) &&
       (enc_equivalence_at ea sts stt (num 0) (num 0)) &&
       sts.used_gas @@ (forall_vars ea @ [num 0]) ==
       stt.used_gas @@ (forall_vars ea @ [num 0]))
  in
  let m = solve_model_exn [c] in
  find_min_gas ea sp tp sts stt m

let update_gas_row sg tg = function
  | [sbc; tbc; toc; tic; _; _; _; ko; tv] ->
    [sbc; tbc; toc; tic; [%show: int] sg; [%show: int] tg; [%show: int] (sg - tg); ko; tv]
  | _ -> failwith "row does not match result format"

let compute_gas_row r =
  let sg = Csv.Row.find r "source gas"
  and tg = Csv.Row.find r "target gas"
  and tv = Csv.Row.find r "translation validation" in
  if (sg = "tbc" || tg = "tbc") && tv = "true" then
    let sbc = Csv.Row.find r "source bytecode"
    and tbc = Csv.Row.find r "target bytecode" in
    Out_channel.prerr_endline ("Processing " ^ sbc);
    let (sgc, tgc) =
      compute_gas
        (Sedlexing.Latin1.from_string sbc |> Parser.parse)
        (Sedlexing.Latin1.from_string tbc |> Parser.parse)
    in
    update_gas_row sgc tgc (Csv.Row.to_list r)
  else
    Csv.Row.to_list r

let () =
  let open Command.Let_syntax in
  Command.basic ~summary:"Compute gas cost and savings for snippets involving SSTORE"
    [%map_open
      let f = anon ("CSVFILE" %: string)
      and outfile = flag "outfile" (required string)
          ~doc:"f.csv save result to f.csv"
      in
      fun () ->
        let header = [
          "source bytecode"
        ; "target bytecode"
        ; "target opcode"
        ; "target instruction count"
        ; "source gas"
        ; "target gas"
        ; "gas saved"
        ; "known optimal"
        ; "translation validation"
        ]
        in
        let csv = Csv.Rows.load ~header:header f in
        let computed = List.map csv ~f:compute_gas_row in
        let out_channel = Csv.to_channel (Out_channel.create outfile) in
        Csv.output_all out_channel computed;
        Csv.close_out out_channel
    ]
  |> Command.run
