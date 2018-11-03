open Core
open Z3util
open Program
open Evmenc

let set_options stackes stackas nobv =
  Option.iter stackes ~f:(fun stackes -> ses := stackes; sesort := bv_sort !ses);
  Option.iter stackas ~f:(fun stackas -> sas := stackas; sasort := bv_sort !sas);
  if nobv then (sesort := int_sort; sasort := int_sort) else ()

let super_optimize_encbl p sis pm pc psmt =
  let log b s =
    if b then
      begin
        Out_channel.output_string Out_channel.stderr s;
        Out_channel.flush Out_channel.stderr
      end
    else ()
  in
  let rec sopt p gas_saved =
    let ea = mk_enc_consts p sis in
    let c = enc_super_opt ea in
    log pc ("Constraint generated:\n" ^ Z3.Expr.to_string (Z3.Expr.simplify c None) ^ "\n\n");
    log psmt ("SMT-LIB Benchmark generated:\n" ^
              Z3.SMT.benchmark_to_smtstring !ctxt "" "" "unknown" "" []
                (Z3.Expr.simplify c None) ^ "\n\n");
    match solve_model [c] with
    | Some m ->
      log pm ("Model found:\n" ^ Z3.Model.to_string m ^ "\n\n");
      let p' = dec_super_opt ea m in
      let g = Program.total_gas_cost p - Program.total_gas_cost p' in
      sopt p' (Option.merge gas_saved (Some g) ~f:(+))
    | None -> (p, gas_saved)
  in
  sopt p None

let super_optimize_bb sis pm pc psmt = function
  | Next p ->
    let (p', _) = super_optimize_encbl p sis pm pc psmt in Next p'
  | Terminal (p, i) ->
    let (p', _) = super_optimize_encbl p sis pm pc psmt in Terminal (p', i)
  | NotEncodable p -> NotEncodable p

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
          ~doc:"ses number of bits used for stack elements"
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
      and progr = anon ("PROGRAM" %: string)
      in
      fun () ->
        set_options stackes stackas nobv;
        let buf =
          if direct then Sedlexing.Latin1.from_string progr
          else Sedlexing.Latin1.from_channel (In_channel.create progr)
        in
        let p = Parser.parse buf in
        let bbs = Program.split_into_bbs p in
        let bbs_opt =
          match opt_mode with
          | NO -> bbs
          | UNBOUNDED ->
            List.map bbs ~f:(super_optimize_bb `All p_model p_constr p_smt)
        in
        match csv with
        | None -> Program.pp Format.std_formatter (concat_bbs bbs_opt)
        | Some fn -> Csv.save fn
                       (["byte code";"op code";"type";"instruction count"] ::
                         (List.map bbs ~f:stats_bb))
    ]
  |> Command.run ~version:"0.1"
