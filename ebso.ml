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
open Printer

type output_options =
  { pmodel : bool
  ; psmt : bool
  ; pcnstrnt : bool
  ; pinter : bool
  ; csv: string option
  }

let outputcfg =
  ref {pmodel = false; psmt = false; pcnstrnt = false; pinter = false; csv = None}

let set_options wordsize stackas pm psmt pc pinter csv =
  outputcfg := {pmodel = pm; psmt = psmt; pcnstrnt = pc; pinter = pinter; csv = csv};
  Option.iter stackas ~f:(fun stackas -> set_sas stackas);
  set_wsz wordsize

let log e =
  let log b s = if b then Out_channel.prerr_endline s else () in
  match e with
  | `Constraint c ->
    log !outputcfg.pcnstrnt (show_constraint c);
    log !outputcfg.psmt (show_smt_benchmark c)
  | `Model m -> log !outputcfg.pmodel (show_model m)

let output_step hist hist_bbs =
  match !outputcfg.csv with
  | None -> print_step (List.hd_exn hist) !outputcfg.pinter
  | Some fn -> Csv.save fn (create_result (hist @ List.concat hist_bbs))

let add_step step = function
  | h when !outputcfg.pinter -> step :: h
  | s :: ss ->
    let tv =
      if Option.is_some step.tval then step.tval
      else if step.input = s.opt then s.tval else None
    in
    {step with input = s.input; tval = tv} :: ss
  | [] -> [step]

let is_translation_valid s t =
  let s' = Program.const_to_val s and t' = Program.const_to_val t in
  let c = enc_trans_val (mk_enc_consts s' (`User [])) t' in
  match solve_model [c] with
    | None -> true
    | Some _ -> false

let tvalidate s t sz =
  let oldwsz = !wsz in
  set_wsz sz;
  let tv = is_translation_valid s t in
  set_wsz oldwsz; tv

let super_optimize_encbl p cis tval hist_bbs =
  let rec sopt p hist =
    let ea = mk_enc_consts p cis in
    let c = enc_super_opt ea in
    log (`Constraint c);
    match solve_model [c] with
    | Some m ->
      log (`Model m);
      let p' = dec_super_opt ea m in
      let tv = Option.map tval ~f:(tvalidate ea.p p') in
      let stp = {input = p; opt = p'; optimal = false; tval = tv} in
      let hist = add_step stp hist in
      output_step hist hist_bbs;
      (* if translation validation failed discard program and increase wordsize by 1 *)
      begin
        match tv with
        | Some false ->
          begin
            set_wsz (!wsz + 1);
            sopt (Program.val_to_const !wsz (Program.const_to_val p)) hist
          end
        | _ -> sopt p' hist
      end
    | None ->
      let stp = {input = p; opt = p; optimal = true; tval = None} in
      let hist = add_step stp hist in
      output_step hist hist_bbs;
      hist :: hist_bbs
  in
  sopt p []

let super_optimize_bb cis tval hist_bbs bb = match ebso_snippet bb with
  | Some p ->  super_optimize_encbl p cis tval hist_bbs
  | None   -> hist_bbs

let classic_super_optimize_encbl p cis tval hist_bbs =
  let rec sopt p g gm cps =
    let ea = mk_enc_consts p cis in
    match cps with
    | [] ->
      let (cps, m') = Program.enumerate g ea.cis gm in
      sopt p (g + 1) m' cps
    | cp :: cps ->
      let js = List.init (List.length cp) ~f:(fun i -> intconst ("j" ^ Int.to_string i)) in
      let c = enc_classic_so_test ea cp js in
      log (`Constraint c);
      match solve_model [c] with
      | None -> sopt p g gm cps
      | Some m ->
        log (`Model m);
        let p' = dec_classic_super_opt ea m cp js in
        let tv = Option.map tval ~f:(tvalidate ea.p p') in
        match tv with
        | Some false -> sopt p g gm cps
        | _ ->
          let s = {input = p; opt = p'; optimal = true; tval = tv} in
          output_step [s] hist_bbs;
          [s] :: hist_bbs
  in
  sopt p 0 (Int.Map.set Int.Map.empty ~key:0 ~data:[[]]) []

let classic_super_optimize_bb cis tval hist_bbs bb = match ebso_snippet bb with
  | Some p -> classic_super_optimize_encbl p cis tval hist_bbs
  | None -> hist_bbs

type opt_mode =
  | NO
  | UNBOUNDED
  | CLASSIC
[@@deriving show { with_path = false }]

let opt_mode_of_string = function
  | "NO" -> NO
  | "UNBOUNDED" -> UNBOUNDED
  | "BASIC" -> CLASSIC
  | _ -> failwith "Unknown optimization mode"

let () =
  let open Command.Let_syntax in
  Command.basic ~summary:"ebso: An EVM Bytecode Super Optimizer"
    [%map_open
      let direct = flag "direct" no_arg
          ~doc:"do not read program from file, but interpret input as program \
                directly"
      and p_model = flag "print-model" no_arg
          ~doc:"print model found by solver"
      and p_constr = flag "print-constraint" no_arg
          ~doc:"print constraint given to solver"
      and p_smt = flag "print-smt" no_arg
          ~doc:"print constraint given to solver in SMT-LIB format"
      and wordsize = flag "word-size" (optional int)
          ~doc:"wsz word size, i.e., number of bits used for stack elements"
      and stackas = flag "stack-address-size" (optional int)
          ~doc:"sas number of bits used for addressing stack elements \
                (i.e. stack then has 2^sas elements)"
      and opt_mode = flag "optimize"
          (optional_with_default UNBOUNDED (Arg_type.create opt_mode_of_string))
          ~doc:"mode optimize NO | UNBOUNDED | BASIC"
      and csv = flag "csv" (optional string)
          ~doc:"filename write output to csv file"
      and p_inter = flag "print-intermediate" no_arg
          ~doc:"print intermediate results"
      and tval = flag "translation-validation" (optional int)
          ~doc:"n do translation validation for word size n after optimization"
      and progr = anon ("PROGRAM" %: string)
      in
      fun () ->
        let buf =
          if direct then Sedlexing.Latin1.from_string progr
          else Sedlexing.Latin1.from_channel (In_channel.create progr)
        in
        let p = Parser.parse buf in
        let wordsize = match wordsize with
          | Some wsz -> wsz
          | None -> Program.compute_word_size p 256
        in
        set_options wordsize stackas p_model p_smt p_constr p_inter csv;
        let p = Program.val_to_const !wsz p in
        let bbs = Program.split_into_bbs p in
        match opt_mode with
        | NO ->
          begin
            match csv with
            | Some fn -> Csv.save fn (Printer.create_ebso_snippets bbs)
            | None -> Program.pp Format.std_formatter (concat_bbs bbs);
          end
        | UNBOUNDED ->
          List.fold_left bbs ~init:[] ~f:(super_optimize_bb `All tval) |> ignore
        | CLASSIC ->
          List.fold_left bbs ~init:[] ~f:(classic_super_optimize_bb `All  tval) |> ignore
    ]
  |> Command.run ~version:"1.0"
