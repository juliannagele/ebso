open Core
open Z3util
open Program
open Evmenc

type output_options =
  { pmodel : bool
  ; psmt : bool
  ; pcnstrnt : bool
  ; pinter : bool
  ; csv: string option
  }

let outputcfg =
  ref {pmodel = false; psmt = false; pcnstrnt = false; pinter = false; csv = None}

let set_options stackes stackas nobv pm psmt pc pinter csv =
  outputcfg := {pmodel = pm; psmt = psmt; pcnstrnt = pc; pinter = pinter; csv = csv};
  Option.iter stackes ~f:(fun stackes -> ses := stackes; sesort := bv_sort !ses);
  Option.iter stackas ~f:(fun stackas -> sas := stackas; sasort := bv_sort !sas);
  if nobv then (sesort := int_sort; sasort := int_sort) else ()

let log e =
  let log b s = if b then Out_channel.prerr_endline s else () in
  match e with
  | `Constraint c ->
    log !outputcfg.pcnstrnt
      ("Constraint generated:\n" ^ Z3.Expr.to_string (Z3.Expr.simplify c None) ^ "\n");
    log !outputcfg.psmt ("SMT-LIB Benchmark generated:\n" ^
                         Z3.SMT.benchmark_to_smtstring !ctxt "" "" "unknown" "" []
                           (Z3.Expr.simplify c None))
  | `Model m -> log !outputcfg.pmodel ("Model found:\n" ^ Z3.Model.to_string m ^ "\n")

type step = {input: Program.t; opt: Program.t; optimal: bool}

let step_to_csv_string step =
  let g = (total_gas_cost step.input - total_gas_cost step.opt) in
  [show_hex step.input; show_hex step.opt; Int.to_string g; Bool.to_string step.optimal]

let print_step step =
  let g = (total_gas_cost step.input - total_gas_cost step.opt) in
  if not !outputcfg.pinter && not step.optimal then ()
  else
    Out_channel.printf "Optimized\n%sto\n%sSaved %i gas"
      (Program.show step.input) (Program.show step.opt) g;
  if step.optimal then
    Out_channel.print_endline ", this instruction sequence is optimal."
  else Out_channel.print_endline "."

let output_step hist hist_bbs =
  match !outputcfg.csv with
  | None -> print_step (List.hd_exn hist)
  | Some fn ->
    Csv.save fn (["input";"optimized";"gas saved"; "known optimal"] ::
                 List.rev_map ~f:step_to_csv_string (hist @ List.concat hist_bbs))

let add_step step = function
  | h when !outputcfg.pinter -> step :: h
  | s :: ss -> {step with input = s.input} :: ss
  | [] -> [step]

let super_optimize_encbl p sis hist_bbs =
  let rec sopt p hist =
    let ea = mk_enc_consts p sis in
    let c = enc_super_opt ea in
    log (`Constraint c);
    match solve_model [c] with
    | Some m ->
      log (`Model m);
      let p' = dec_super_opt ea m in
      let hist = add_step {input = p; opt = p'; optimal = false} hist in
      output_step hist hist_bbs;
      sopt p' hist
    | None ->
      let hist = add_step {input = p; opt = p; optimal = true} hist in
      output_step hist hist_bbs;
      hist :: hist_bbs
  in
  sopt p []

let super_optimize_bb sis hist_bbs = function
  | Next p -> super_optimize_encbl p sis hist_bbs
  | Terminal (p, _) -> super_optimize_encbl p sis hist_bbs
  | NotEncodable _ -> hist_bbs

let stats_bb bb =
  let len p = Int.to_string (List.length p) in
  match bb with
  | Terminal (p, i) ->
    [Program.show_hex (p @ [i]); Program.show_h (p @ [i]); "Terminal"; len (p @ [i])]
  | Next p ->
    [Program.show_hex p; Program.show_h p; "Next"; len p]
  | NotEncodable p ->
    [Program.show_hex p; Program.show_h p; "NotEncodable"; len p]

type opt_mode =
  | NO
  | UNBOUNDED
[@@deriving show { with_path = false }]

let opt_mode_of_string = function
  | "NO" -> NO
  | "UNBOUNDED" -> UNBOUNDED
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
      and stackes = flag "stack-element-size" (optional int)
          ~doc:"ses number of bits used for stack elements \
                (fits arguments of PUSH by modulo 2^ses)"
      and stackas = flag "stack-address-size" (optional int)
          ~doc:"sas number of bits used for addressing stack elements \
                (i.e. stack then has 2^sas elements)"
      and nobv = flag "no-bitvectors" no_arg
          ~doc:"do not use bit vectors, but integers everywhere \
                (stack-element-size and stack-address-size have no effect)"
      and opt_mode = flag "optimize"
          (optional_with_default UNBOUNDED (Arg_type.create opt_mode_of_string))
          ~doc:"mode optimize NO | UNBOUNDED"
      and csv = flag "csv" (optional string)
          ~doc:"filename write output to csv file"
      and p_inter = flag "print-intermediate" no_arg
          ~doc:"print intermediate results"
      and progr = anon ("PROGRAM" %: string)
      in
      fun () ->
        set_options stackes stackas nobv p_model p_smt p_constr p_inter csv;
        let buf =
          if direct then Sedlexing.Latin1.from_string progr
          else Sedlexing.Latin1.from_channel (In_channel.create progr)
        in
        let p = Parser.parse buf in
        let p = if Option.is_some stackes then Program.mod_to_ses !ses p else p in
        let bbs = Program.split_into_bbs p in
        match opt_mode with
        | NO ->
          begin
            match csv with
            | Some fn -> Csv.save fn
                           (["byte code";"op code";"type";"instruction count"] ::
                            (List.map bbs ~f:stats_bb))
            | None -> Program.pp Format.std_formatter (concat_bbs bbs);
          end
        | UNBOUNDED -> List.fold_left bbs ~init:[] ~f:(super_optimize_bb `All) |> ignore
    ]
  |> Command.run ~version:"0.1"
