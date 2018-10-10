open Core
open Z3util
open Evmenc

let super_optimize p sis pm pc =
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
      and stackes = flag "stack-element-size" (optional int)
          ~doc:"ses number of bits used for stack elements"
      and stackas = flag "stack-address-size" (optional int)
          ~doc:"sas number of bits used for addressing stack elements \
                (i.e. stack then has 2^sas elements)"
      and progr = anon ("PROGRAM" %: string)
      in
      fun () ->
        begin
          match stackes with
          | None -> ()
          | Some stackes -> ses := stackes
        end;
        begin
          match stackas with
          | None -> ()
          | Some stackas -> sas := stackas
        end;
        let progr =
          if direct then progr else In_channel.read_all progr
        in
        let p = Sexp.of_string progr |> progr_of_sexp in
        super_optimize p `All p_model p_constr
        |> show_progr
        |> print_string
    ]
  |> Command.run ~version:"0.1"
