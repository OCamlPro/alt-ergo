(******************************************************************************)
(*                                                                            *)
(*     The Alt-Ergo theorem prover                                            *)
(*     Copyright (C) 2006-2013                                                *)
(*                                                                            *)
(*     Sylvain Conchon                                                        *)
(*     Evelyne Contejean                                                      *)
(*                                                                            *)
(*     Francois Bobot                                                         *)
(*     Mohamed Iguernelala                                                    *)
(*     Stephane Lescuyer                                                      *)
(*     Alain Mebsout                                                          *)
(*                                                                            *)
(*     CNRS - INRIA - Universite Paris Sud                                    *)
(*                                                                            *)
(*     This file is distributed under the terms of the Apache Software        *)
(*     License version 2.0                                                    *)
(*                                                                            *)
(*  ------------------------------------------------------------------------  *)
(*                                                                            *)
(*     Alt-Ergo: The SMT Solver For Software Verification                     *)
(*     Copyright (C) 2013-2018 --- OCamlPro SAS                               *)
(*                                                                            *)
(*     This file is distributed under the terms of the Apache Software        *)
(*     License version 2.0                                                    *)
(*                                                                            *)
(******************************************************************************)

open AltErgoLib
open Options
open D_loop

type solver_ctx = {
  ctx    : Commands.sat_tdecl list;
  local  : Commands.sat_tdecl list;
  global : Commands.sat_tdecl list;
}

let empty_solver_ctx = { ctx = []; local = []; global = []; }

(* Internal state while iterating over input statements *)
type 'a state = {
  env : 'a;
  solver_ctx: solver_ctx;
}

let main () =
  let module SatCont =
    (val (Sat_solver.get_current ()) : Sat_solver_sig.SatContainer) in

  let module TH =
    (val
      (if Options.get_no_theory() then (module Theory.Main_Empty : Theory.S)
       else (module Theory.Main_Default : Theory.S)) : Theory.S ) in

  let module SAT = SatCont.Make(TH) in

  let module FE = Frontend.Make (SAT) in

  let solve all_context (cnf, goal_name) =
    let used_context = FE.choose_used_context all_context ~goal_name in
    let consistent_dep_stack = Stack.create () in
    Signals_profiling.init_profiling ();
    try
      if Options.get_timelimit_per_goal() then
        begin
          Options.Time.start ();
          Options.Time.set_timeout ~is_gui:false (Options.get_timelimit ());
        end;
      SAT.reset_refs ();
      let _ =
        List.fold_left
          (FE.process_decl FE.print_status used_context consistent_dep_stack)
          (SAT.empty (), true, Explanation.empty) cnf
      in
      if Options.get_timelimit_per_goal() then
        Options.Time.unset_timeout ~is_gui:false;
      if Options.get_profiling() then
        Profiling.print true
          (Steps.get_steps ())
          (Signals_profiling.get_timers ())
          (get_fmt_err ())
    with Util.Timeout ->
      if not (Options.get_timelimit_per_goal()) then exit 142
  in

  let typed_loop all_context state td =
    if get_type_only () then state else begin
      match td.Typed.c with
      | Typed.TGoal (_, kind, name, _) ->
        let l =
          state.solver_ctx.local @
          state.solver_ctx.global @
          state.solver_ctx.ctx
        in
        let cnf = List.rev @@ Cnf.make l td in
        let () = solve all_context (cnf, name) in
        begin match kind with
          | Ty.Check
          | Ty.Cut ->
            { state with solver_ctx = { state.solver_ctx with local = []; }}
          | Ty.Thm | Ty.Sat ->
            { state with solver_ctx = {
                  state.solver_ctx with global = []; local = [];
                }}
        end
      | Typed.TAxiom (_, s, _, _) when Ty.is_global_hyp s ->
        let cnf = Cnf.make state.solver_ctx.global td in
        { state with solver_ctx = { state.solver_ctx with global = cnf; }}
      | Typed.TAxiom (_, s, _, _) when Ty.is_local_hyp s ->
        let cnf = Cnf.make state.solver_ctx.local td in
        { state with solver_ctx = { state.solver_ctx with local = cnf; }}
      | _ ->
        let cnf = Cnf.make state.solver_ctx.ctx td in
        { state with solver_ctx = { state.solver_ctx with ctx = cnf; }}
    end
  in

  let ae_fe filename frontend =
    let (module I : Input.S) = Input.find frontend in

    let parsed () =
      try
        Options.Time.start ();
        if not (Options.get_timelimit_per_goal()) then
          Options.Time.set_timeout ~is_gui:false (Options.get_timelimit ());

        Options.set_is_gui false;
        Signals_profiling.init_profiling ();

        let preludes = Options.get_preludes () in
        I.parse_files ~filename ~preludes
      with
      | Util.Timeout ->
        FE.print_status (FE.Timeout None) 0;
        exit 142
      | Parsing.Parse_error ->
        Printer.print_err "%a" Errors.report
          (Syntax_error ((Lexing.dummy_pos,Lexing.dummy_pos),""));
        exit 1
      | Errors.Error e ->
        Printer.print_err "%a" Errors.report e;
        exit 1
    in

    let all_used_context = FE.init_all_used_context () in
    if Options.get_timelimit_per_goal() then
      FE.print_status FE.Preprocess 0;
    let assertion_stack = Stack.create () in
    let typing_loop state p =
      if get_parse_only () then state else begin
        try
          let l, env = I.type_parsed state.env assertion_stack p in
          List.fold_left (typed_loop all_used_context) { state with env; } l
        with
        | Errors.Error e ->
          if e != Warning_as_error then
            Printer.print_err "%a" Errors.report e;
          exit 1
      end
    in

    let state = {
      env = I.empty_env;
      solver_ctx = empty_solver_ctx
    } in
    try
      let parsed_seq = parsed () in
      let _ : _ state = Seq.fold_left typing_loop state parsed_seq in
      Options.Time.unset_timeout ~is_gui:false;
    with Util.Timeout ->
      FE.print_status (FE.Timeout None) 0;
      exit 142
  in

  let solver_ctx_key: solver_ctx State.key =
    State.create_key ~pipe:"" "solving_state"
  in
  let debug_parsed_pipe st c =
    if State.get State.debug st then
      Format.eprintf "[logic][parsed][%a] @[<hov>%a@]@."
        Dolmen.Std.Loc.print_compact c.Dolmen.Std.Statement.loc
        Dolmen.Std.Statement.print c;
    st, c
  in
  let debug_typed_pipe st stmt =
    if State.get State.debug st then
      Format.eprintf "[logic][typed][%a] @[<hov>%a@]@\n@."
        Dolmen.Std.Loc.print_compact stmt.Typer_Pipe.loc
        Typer_Pipe.print stmt;
    st, stmt
  in
  let handle_exn _ bt e =
    Printexc.raise_with_backtrace e bt
  in
  let finally ~handle_exn st e =
    match e with
    | Some (bt, exn) -> handle_exn st bt exn; st
    | _ -> st
  in
  let mk_file ?lang ?mode ?(source = `Raw ("", ""))
      ?(loc = Dolmen.Std.Loc.mk_file "") dir: _ State.file =
    { lang; mode; dir; source; loc; }
  in
  let mk_state ?(debug = false) ?(report_style = State.Contextual)
      ?(reports =
        Dolmen_loop.Report.Conf.mk
          ~default:Dolmen_loop.Report.Warning.Status.Enabled)
      ?(max_warn = max_int) ?(time_limit = 300.) ?(size_limit = 1_000_000_000.)
      ?input_mode ?(header_check = false) ?(header_licenses = [])
      ?header_lang_version ?(type_check = true)
      ?(solver_ctx = empty_solver_ctx) path =
    let dir = Filename.dirname path in
    let logic_file =
      mk_file
        ?mode:input_mode
        ~source:(`File (Filename.basename path))
        ~loc:(Dolmen.Std.Loc.mk_file path)
        dir
    in
    let response_file = mk_file dir in
    State.empty
    |> State.set solver_ctx_key solver_ctx
    |> State.init ~debug ~report_style ~reports ~max_warn ~time_limit
      ~size_limit ~logic_file ~response_file
    |> Parser.init
    |> Typer.init
    |> Typer_Pipe.init ~type_check
    |> Header.init ~header_check ~header_licenses ~header_lang_version
  in

  let handle_stmt :
    FE.used_context -> State.t ->
    Typer_Pipe.typechecked Typer_Pipe.stmt -> State.t =
    let goal_cnt = ref 0 in
    fun all_context st td ->
      let solver_ctx = State.get solver_ctx_key st in
      match td with
      (* When the next statement is a goal, the solver is called and provided
         the goal and the current context *)
      | { id = {name = Simple name; _}; contents = `Goal _; _ } ->
        let l =
          solver_ctx.local @
          solver_ctx.global @
          solver_ctx.ctx
        in
        let rev_cnf = D_cnf.make (State.get State.logic_file st).loc l td in
        let cnf = List.rev rev_cnf in
        let () = solve all_context (cnf, name) in
        let rec ng_is_thm rcnf =
          begin match rcnf with
            | Commands.{ st_decl = Query (_, _, (Ty.Thm | Ty.Sat)); _ } :: _ ->
              true
            | Commands.{ st_decl = Query _; _ } :: _ -> false
            | _ :: tl -> ng_is_thm tl
            | _ -> assert false (* unreachable *)
          end
        in
        if ng_is_thm rev_cnf
        then
          State.set solver_ctx_key (
            let solver_ctx = State.get solver_ctx_key st in
            { solver_ctx with global = []; local = [] }
          ) st
        else
          State.set solver_ctx_key (
            let solver_ctx = State.get solver_ctx_key st in
            { solver_ctx with local = [] }
          ) st

      | { id = _; contents = `Hyp _; _ } ->
        let cnf = D_cnf.make (State.get State.logic_file st).loc [] td in
        begin match cnf with
          | [Commands.{ st_decl = Assume (name, _, _); _ } as c]
            when Ty.is_global_hyp name ->
            State.set solver_ctx_key (
              let solver_ctx = State.get solver_ctx_key st in
              { solver_ctx with global = c :: solver_ctx.global }
            ) st
          | [Commands.{ st_decl = Assume (name, _, _); _ } as c]
            when Ty.is_local_hyp name ->
            State.set solver_ctx_key (
              let solver_ctx = State.get solver_ctx_key st in
              { solver_ctx with local = c :: solver_ctx.local }
            ) st
          | _ ->
            State.set solver_ctx_key (
              let solver_ctx = State.get solver_ctx_key st in
              { solver_ctx with ctx = cnf @ solver_ctx.ctx }
            ) st
        end
      | {id = _; contents = `Solve _; loc }
        when (
          match (State.get State.logic_file st).lang with
          | Some (Smtlib2 _) -> true
          | Some _ -> false
          | None -> assert false
          (* unreachable because the file's language is set after parsing *)
        ) ->
        let l =
          solver_ctx.local @
          solver_ctx.global @
          solver_ctx.ctx
        in
        let goal_name = "g_"^ string_of_int (incr goal_cnt; !goal_cnt) in
        let rev_cnf = D_cnf.make (State.get State.logic_file st).loc l
            Typer_Pipe.{
              id = DStd.Id.mk DStd.Namespace.term goal_name;
              contents = `Goal DStd.Expr.Term.(of_cst Const._false);
              loc;
            }
        in
        let cnf = List.rev rev_cnf in
        let () = solve all_context (cnf, goal_name) in
        let rec ng_is_thm rcnf =
          begin match rcnf with
            | Commands.{ st_decl = Query (_, _, (Ty.Thm | Ty.Sat)); _ } :: _ ->
              true
            | Commands.{ st_decl = Query _; _ } :: _ -> false
            | _ :: tl -> ng_is_thm tl
            | _ -> assert false (* unreachable *)
          end
        in
        if ng_is_thm rev_cnf
        then
          State.set solver_ctx_key (
            let solver_ctx = State.get solver_ctx_key st in
            { solver_ctx with global = []; local = [] }
          ) st
        else
          State.set solver_ctx_key (
            let solver_ctx = State.get solver_ctx_key st in
            { solver_ctx with local = [] }
          ) st
      | _ ->
        (* TODO:
           - Separate statements that should be ignored from unsupported
             statements and throw exception or print a warning when an
             unsupported statement is encountered.
           - Support "get-model" statements
        *)
        let cnf =
          D_cnf.make (State.get State.logic_file st).loc
            (State.get solver_ctx_key st).ctx td
        in
        State.set solver_ctx_key (
          let solver_ctx = State.get solver_ctx_key st in
          { solver_ctx with ctx = cnf }
        ) st
  in
  let d_fe filename =
    let st = mk_state filename in
    try
      let st, g = Parser.parse_logic [] st (State.get State.logic_file st) in
      let all_used_context = FE.init_all_used_context () in
      let finally = finally ~handle_exn in
      let _st =
        let open Pipeline in
        run ~finally g st
          (fix
             (op ~name:"expand" Parser.expand)
             (op ~name:"debug_pre" debug_parsed_pipe
              @>>> op ~name:"typecheck" Typer_Pipe.typecheck
              @>|> op ~name:"debug_post" debug_typed_pipe
              @>>> op (fun st stmt -> handle_stmt all_used_context st stmt, ())
              @>>> _end))
      in
      let st = Header.check st in
      ignore (State.flush st ())
    with exn ->
      let bt = Printexc.get_raw_backtrace () in
      handle_exn st bt exn
  in

  let filename = get_file () in
  match get_frontend () with
  | "dolmen" -> d_fe filename
  | frontend -> ae_fe filename frontend
