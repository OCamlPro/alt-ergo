open Cmdliner

let mk_state input =
  let open Loop in
  let dir = Filename.dirname input in
  let base = Filename.basename input in
  let logic_file = State.mk_file dir (`File base) in
  let response_file = State.mk_file dir (`Raw ("", "")) in
  State.empty
  |> State.set Header.header_state Dolmen_loop.Headers.empty
  |> State.init ~debug:false ~report_style:Contextual
       ~reports:
         (Dolmen_loop.Report.Conf.mk
            ~default:Dolmen_loop.Report.Warning.Status.Disabled)
       ~max_warn:max_int ~time_limit:infinity ~size_limit:infinity
       ~response_file
  |> State.set State.logic_file logic_file
  |> Parser.init
  |> Typer.init
       ~ty_state:(Dolmen_loop.Typer.new_state ())
       ~smtlib2_forced_logic:None
  |> Typer.init_pipe ~type_check:true
  |> Header.init ~header_check:false ~header_licenses:[]
       ~header_lang_version:None

let file_arg =
  Arg.(
    required
    & pos 0 (some string) None
    & info [] ~docv:"FILE" ~doc:"Input SMT-LIB2 file.")

let pow2_builtin_arg =
  Arg.(
    value & opt bool true
    & info ["pow2-builtin"] ~docv:"BOOL"
        ~doc:
          "Use the builtin operator `int.pow2` instead of the axiomatized \
           `pow2`.")

let sqrt_builtin_arg =
  Arg.(
    value & opt bool true
    & info ["sqrt-builtin"] ~docv:"BOOL"
        ~doc:
          "Use the builtin operator `sqrt_real` instead of the axiomatized \
           `sqrt2`.")

let inline_functions_arg =
  Arg.(
    value & opt bool true
    & info ["inline-functions"] ~docv:"BOOL"
        ~doc:
          "Eagerly inline calls to defined functions. (The functions are \
           expected to be non-recursive)")

let select_triggers_arg =
  Arg.(
    value & opt bool true
    & info ["select-triggers"] ~docv:"BOOL"
        ~doc:
          "Automatically select a :pattern trigger for every generated axiom \
           that doesn't already have one.")

let cmd run =
  let term =
    Term.(
      const run $ file_arg $ pow2_builtin_arg $ sqrt_builtin_arg
      $ inline_functions_arg $ select_triggers_arg)
  in
  Cmd.v
    (Cmd.info "fpa-gen"
       ~doc:
         "Generalize FPA preludes by adding eb/sb parameters to FP operations \
          and quantifying the axioms over eb and sb.")
    term
