open Core
open Z3util
open Evmenc

let super_optimize p sis pm pc psmt =
  let log b s =
    if b then
      begin
        Out_channel.output_string  Out_channel.stderr s;
        Out_channel.flush Out_channel.stderr
      end
    else ()
  in
  let ea = mk_enc_consts p sis in
  let c = enc_super_opt ea in
  log pc ("Constraint generated:\n" ^ Z3.Expr.to_string (Z3.Expr.simplify c None) ^ "\n\n");
  log psmt ("SMT-LIB Benchmark generated:\n" ^
            Z3.SMT.benchmark_to_smtstring !ctxt "" "" "unknown" "" []
              (Z3.Expr.simplify c None) ^ "\n\n");
  let m = solve_model_exn [c] in
  log pm ("Model found:\n" ^ Z3.Model.to_string m ^ "\n\n");
  (dec_super_opt ea m)

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
      and progr = anon ("PROGRAM" %: string)
      in
      fun () ->
        begin
          match stackes with
          | None -> ()
          | Some stackes -> sesort := bv_sort stackes
        end;
        begin
          match stackas with
          | None -> ()
          | Some stackas -> sasort := bv_sort stackas
        end;
        begin if nobv then (sesort := int_sort; sasort := int_sort) else () end;
        let buf =
          if direct then Sedlexing.Latin1.from_string progr
          else Sedlexing.Latin1.from_channel (In_channel.create progr)
        in
        let p = Parser.parse buf in
        let p_opt = super_optimize p `All p_model p_constr p_smt in
        Program.pp Format.std_formatter p_opt
    ]
  |> Command.run ~version:"0.1"
