let finally st = function None -> st | Some (_bt, exn) -> raise exn

let rewrite_state_key : Rewrite.state Loop.State.key =
  Loop.State.create_key ~pipe:"fpa" "rewrite_state"

let handle_stmt rewrite_ctx st
    (stmts : Loop.Typer.typechecked Loop.Typer.stmt list) =
  let st, stmts' =
    let rw_st = Loop.State.get rewrite_state_key st in
    let rw_st', result = Rewrite.run rewrite_ctx rw_st stmts in
    Loop.State.set rewrite_state_key rw_st' st, result
  in
  let st, _ = Loop.Export.export st stmts' in
  st, ()

let run_pipeline ~pow2_builtin ~sqrt_builtin ~inline_functions ~select_triggers
    input st =
  let rewrite_ctx =
    Rewrite.create_ctx ~pow2_builtin ~sqrt_builtin ~inline_functions
      ~select_triggers ()
  in
  let ae_builtins =
    Loop.State.mk_file (Filename.dirname input) (`File "ae_builtins.psmt2")
  in
  let g =
    Loop.Parser.parse_logic ~preludes:[ae_builtins]
      (Loop.State.get Loop.State.logic_file st)
  in
  let output_file : Dolmen_loop.Export.file =
    Loop.State.{ lang = Some (Loop.Logic.Smtlib2 `Poly); sink = `Stdout }
  in
  let st = Loop.Export.init ~output_file st in
  let st = Loop.State.set rewrite_state_key Rewrite.init_state st in
  let st =
    let open Loop.Pipeline in
    run ~finally g st
      (fix
         (op ~name:"expand" Loop.Parser.expand)
         (op ~name:"headers" Loop.Header.inspect
         @>>> op ~name:"typecheck" Loop.Typer.typecheck
         @>|> op (handle_stmt rewrite_ctx)
         @>>> _end))
  in
  let _st = Dolmen_loop.State.flush st () in
  ()

let run input pow2_builtin sqrt_builtin inline_functions select_triggers =
  let state = Options.mk_state input in
  run_pipeline ~pow2_builtin ~sqrt_builtin ~inline_functions ~select_triggers
    input state

let () =
  match Cmdliner.Cmd.eval_value (Options.cmd run) with
  | Ok (`Version | `Help) -> exit 0
  | Error (`Parse | `Term | `Exn) -> exit 1
  | Ok (`Ok ()) -> ()
