(**************************************************************************)
(*                                                                        *)
(*     Alt-Ergo: The SMT Solver For Software Verification                 *)
(*     Copyright (C) 2013-2023 --- OCamlPro SAS                           *)
(*                                                                        *)
(*     This file is distributed under the terms of OCamlPro               *)
(*     Non-Commercial Purpose License, version 1.                         *)
(*                                                                        *)
(*     As an exception, Alt-Ergo Club members at the Gold level can       *)
(*     use this file under the terms of the Apache Software License       *)
(*     version 2.0.                                                       *)
(*                                                                        *)
(*     ---------------------------------------------------------------    *)
(*                                                                        *)
(*     The Alt-Ergo theorem prover                                        *)
(*                                                                        *)
(*     Sylvain Conchon, Evelyne Contejean, Francois Bobot                 *)
(*     Mohamed Iguernelala, Stephane Lescuyer, Alain Mebsout              *)
(*                                                                        *)
(*     CNRS - INRIA - Universite Paris Sud                                *)
(*                                                                        *)
(*     Until 2013, some parts of this code were released under            *)
(*     the Apache Software License version 2.0.                           *)
(*                                                                        *)
(*     ---------------------------------------------------------------    *)
(*                                                                        *)
(*     More details can be found in the directory licenses/               *)
(*                                                                        *)
(**************************************************************************)

open AltErgoLib
open Options
open D_loop

type solver_ctx = {
  ctx    : Commands.sat_tdecl list;
  local  : Commands.sat_tdecl list;
  global : Commands.sat_tdecl list;
}

let is_solver_ctx_empty = function
    { ctx = []; local = []; global = [] } -> true
  | _ -> false

type 'a sat_module = (module Sat_solver_sig.S with type t = 'a)

type any_sat_module = (module Sat_solver_sig.S)

(* Internal state while iterating over input statements *)
type 'a state = {
  env : 'a;
  solver_ctx: solver_ctx;
  sat_solver : any_sat_module;
}

let empty_solver_ctx = {
  ctx = [];
  local = [];
  global = [];
}

let recoverable_error ?(code = 1) =
  Format.kasprintf (fun msg ->
      let () =
        if msg <> "" then
          match Options.get_output_format () with
          | Smtlib2 -> Printer.print_smtlib_err "%s" msg
          | _ -> Printer.print_err "%s" msg
      in
      if Options.get_exit_on_error () then exit code)

let fatal_error ?(code = 1) =
  Format.kasprintf (fun msg -> recoverable_error ~code "%s" msg; exit code)

let exit_as_timeout () = fatal_error ~code:142 "timeout"

let warning (msg : ('a, Format.formatter, unit, unit, unit, 'b) format6) : 'a =
  if Options.get_warning_as_error () then
    recoverable_error msg
  else
    Printer.print_wrn msg

let unsupported_opt opt =
  let () =
    match Options.get_output_format () with
    | Options.Smtlib2 -> Printer.print_std "unsupported"
    | _ -> ()
  in
  warning "unsupported option %s" opt

(* We currently use the full state of the solver as model. *)
type model = Model : 'a sat_module * 'a -> model

let main () =
  let () = Dolmen_loop.Code.init [] in

  let make_sat () =
    let module SatCont =
      (val (Sat_solver.get_current ()) : Sat_solver_sig.SatContainer) in

    let module TH =
      (val
        (if Options.get_no_theory() then (module Theory.Main_Empty : Theory.S)
         else (module Theory.Main_Default : Theory.S)) : Theory.S ) in

    (module SatCont.Make(TH) : Sat_solver_sig.S)
  in

  let solve (module SAT : Sat_solver_sig.S) all_context (cnf, goal_name) =
    let module FE = Frontend.Make (SAT) in
    if Options.get_debug_commands () then
      Printer.print_dbg "@[<v 2>goal %s:@ %a@]@."
        ~module_name:"Solving_loop" ~function_name:"solve"
        goal_name
        Fmt.(list ~sep:sp Commands.print) cnf;
    let used_context = Frontend.choose_used_context all_context ~goal_name in
    let consistent_dep_stack = Stack.create () in
    Signals_profiling.init_profiling ();
    try
      if Options.get_timelimit_per_goal() then
        begin
          Options.Time.start ();
          Options.Time.set_timeout (Options.get_timelimit ());
        end;
      SAT.reset_refs ();
      let _, consistent, _ =
        List.fold_left
          (FE.process_decl
             Frontend.print_status used_context consistent_dep_stack)
          (SAT.empty (), `Unknown (SAT.empty ()), Explanation.empty) cnf
      in
      if Options.get_timelimit_per_goal() then
        Options.Time.unset_timeout ();
      if Options.get_profiling() then
        Profiling.print true
          (Steps.get_steps ())
          (Options.Output.get_fmt_diagnostic ());
      (* If the status of the SAT environment is inconsistent,
         we have to drop the partial model in order to prevent
         printing wrong model. *)
      match consistent with
      | `Sat partial_model | `Unknown partial_model ->
        Some (Model ((module SAT), partial_model))
      | `Unsat -> None
    with Util.Timeout ->
      if not (Options.get_timelimit_per_goal()) then exit_as_timeout ();
      None
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
        let _ = solve state.sat_solver all_context (cnf, name) in
        begin match kind with
          | Ty.Check
          | Ty.Cut ->
            { state with solver_ctx =
                           { state.solver_ctx with local = []}}
          | Ty.Thm | Ty.Sat ->
            { state with solver_ctx = {
                  state.solver_ctx with global = []; local = []}}
        end
      | Typed.TAxiom (_, s, _, _) when Ty.is_global_hyp s ->
        let cnf = Cnf.make state.solver_ctx.global td in
        { state with solver_ctx = { state.solver_ctx with global = cnf; }}
      | Typed.TAxiom (_, s, _, _) when Ty.is_local_hyp s ->
        let cnf = Cnf.make state.solver_ctx.local td in
        { state with solver_ctx = { state.solver_ctx with local = cnf; }}
      | Typed.TReset _ ->
        { state with solver_ctx = {ctx = []; local = []; global = []}}
      | Typed.TExit _ -> raise Exit
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
          Options.Time.set_timeout (Options.get_timelimit ());

        Signals_profiling.init_profiling ();

        let with_opt (get, set) v f =
          let v' = get () in
          set v;
          Fun.protect
            ~finally:(fun () -> set v')
            f
        in
        let with_infer_output_format =
          with_opt Options.(get_infer_output_format, set_infer_output_format)
        in
        let with_input_format =
          with_opt Options.(get_input_format, set_input_format)
        in
        let theory_preludes =
          Options.get_theory_preludes ()
          |> List.to_seq
          |> Seq.flat_map (fun theory ->
              let filename = Theories.filename theory in
              let content = Theories.content theory in
              with_input_format None @@ fun () ->
              with_infer_output_format false @@ fun () ->
              I.parse_file
                ~content
                ~format:(Some (Filename.extension filename)))
        in
        let preludes = Options.get_preludes () in
        Compat.Seq.append theory_preludes @@
        I.parse_files ~filename ~preludes
      with
      | Util.Timeout ->
        Frontend.print_status (Timeout None) 0;
        exit_as_timeout ()
      | Parsing.Parse_error ->
        (* TODO(Steven): displaying a dummy value is a bad idea.
           This should only be executed with the legacy frontend, which should
           be deprecated in a near future, so this code will be removed (or at
           least, its behavior unspecified). *)
        fatal_error
          "%a"
          Errors.report
          (Syntax_error ((Lexing.dummy_pos,Lexing.dummy_pos),""))
      | Errors.Error e ->
        fatal_error "%a" Errors.report e
    in

    let all_used_context = Frontend.init_all_used_context () in
    if Options.get_timelimit_per_goal() then
      Frontend.print_status Preprocess 0;
    let assertion_stack = Stack.create () in
    let typing_loop state p =
      if get_parse_only () then state else begin
        try
          let l, env = I.type_parsed state.env assertion_stack p in
          List.fold_left (typed_loop all_used_context) { state with env; } l
        with
        | Errors.Error e ->
          let () =
            if e != Warning_as_error then
              recoverable_error "%a" Errors.report e
            else
              recoverable_error ""
          in
          state
        | Exit -> exit 0
      end
    in

    let state = {
      env = I.empty_env;
      solver_ctx = empty_solver_ctx;
      sat_solver = make_sat ();
    } in
    try
      let parsed_seq = parsed () in
      let _ : _ state = Seq.fold_left typing_loop state parsed_seq in
      Options.Time.unset_timeout ();
    with Util.Timeout ->
      Frontend.print_status (Timeout None) 0;
      exit_as_timeout ()
  in

  let solver_ctx_key: solver_ctx State.key =
    State.create_key ~pipe:"" "solving_state"
  in

  let sat_solver_key : (module Sat_solver_sig.S) State.key =
    State.create_key ~pipe:"" "sat_solver"
  in

  let partial_model_key: model option State.key =
    State.create_key ~pipe:"" "sat_state"
  in

  let debug_parsed_pipe st c =
    if State.get State.debug st then
      Format.eprintf "[logic][parsed][%a] @[<hov>%a@]@."
        Dolmen.Std.Loc.print_compact c.Dolmen.Std.Statement.loc
        Dolmen.Std.Statement.print c;
    if get_parse_only () then
      st, `Done ()
    else
      st, `Continue c
  in
  let debug_typed_pipe st stmt =
    if State.get State.debug st then
      Format.eprintf "[logic][typed][%a] @[<hov>%a@]@\n@."
        Dolmen.Std.Loc.print_compact stmt.Typer_Pipe.loc
        Typer_Pipe.print stmt;
    if get_type_only () then
      st, `Done ()
    else
      st, `Continue stmt
  in
  let handle_exn st bt = function
    | Dolmen.Std.Loc.Syntax_error (_, `Regular msg) ->
      recoverable_error "%t" msg; st
    | Util.Timeout ->
      Printer.print_status_timeout None None None None;
      exit_as_timeout ()
    | Errors.Error e ->
      recoverable_error "%a" Errors.report e;
      st
    | Exit -> exit 0
    | _ as exn -> Printexc.raise_with_backtrace exn bt
  in
  let finally ~handle_exn st e =
    match e with
    | Some (bt, exn) -> handle_exn st bt exn
    | _ -> st
  in
  let set_output_format fmt =
    if Options.get_infer_output_format () then
      match fmt with
      | ".ae" -> Options.set_output_format Native
      | ".smt2" | ".psmt2" -> Options.set_output_format Smtlib2
      | s ->
        warning
          "The output format %s is not supported by the Dolmen frontend."
          s
  in
  (* The function In_channel.input_all is not available before OCaml 4.14. *)
  let read_all ch =
    let b = Buffer.create 113 in
    try
      while true do
        Buffer.add_channel b ch 30
      done;
      assert false
    with End_of_file ->
      Buffer.contents b
  in
  let mk_state ?(debug = false) ?(report_style = State.Contextual)
      ?(max_warn = max_int) ?(time_limit = Float.infinity)
      ?(size_limit = Float.infinity) ?(type_check = true)
      ?(solver_ctx = empty_solver_ctx)
      ?(partial_model = None) path =
    let reports =
      Dolmen_loop.Report.Conf.(
        let disable m t =
          match Dolmen_loop.Report.T.find_mnemonic m with
          | Some (`Warning _ as w) -> disable t w
          | _ -> assert false
        in
        mk ~default:Dolmen_loop.Report.Warning.Status.Enabled
        |> disable "unused-type-var"
        |> disable "unused-term-var"
        |> disable "extra-dstr"
        |> disable "shadowing"
      )
    in
    let dir = Filename.dirname path in
    let filename = Filename.basename path in
    let lang =
      match Options.get_input_format () with
      | Some Native -> Some Dl.Logic.Alt_ergo
      | Some Smtlib2 -> Some (Dl.Logic.Smtlib2 `Latest)
      | None | Some (Why3 | Unknown _) -> None
    in
    let source =
      if Filename.check_suffix path ".zip" then (
        Filename.(chop_extension path |> extension) |> set_output_format;
        let content = AltErgoLib.My_zip.extract_zip_file path in
        `Raw (Filename.chop_extension filename, content))
      else (
        Filename.extension path |> set_output_format;
        let content =
          if not (String.equal path "") then
            let cin = open_in path in
            let content = read_all cin in
            close_in cin;
            content
          else read_all stdin
        in
        `Raw (filename, content))
    in
    let logic_file =
      State.mk_file ?lang ~loc:(Dolmen.Std.Loc.mk_file path) dir source
    in
    let response_file = State.mk_file dir (`Raw ("", "")) in
    logic_file,
    State.empty
    |> State.set sat_solver_key (make_sat ())
    |> State.set solver_ctx_key solver_ctx
    |> State.set partial_model_key partial_model
    |> State.init ~debug ~report_style ~reports ~max_warn ~time_limit
      ~size_limit ~response_file
    |> Parser.init
    |> Typer.init
    |> Typer_Pipe.init ~type_check
  in

  let print_wrn_opt ~name loc ty value =
    warning
      "%a The option %s expects a %s, got %a"
      Loc.report loc name ty DStd.Term.print value
  in

  let handle_option st_loc name (value : DStd.Term.t) st =
    match name, value.term with
    (* Smtlib2 regular options *)
    | ":regular-output-channel", Symbol { name = Simple name; _ } ->
      Options.Output.create_channel name
      |> Options.Output.set_regular;
      st
    | ":diagnostic-output-channel", Symbol { name = Simple name; _ } ->
      Options.Output.create_channel name
      |> Options.Output.set_diagnostic;
      st
    | ":produce-models", Symbol { name = Simple "true"; _ } ->
      Options.set_interpretation ILast;
      st
    | ":produce-models", Symbol { name = Simple "false"; _ } ->
      Options.set_interpretation INone;
      st
    | ":produce-unsat-cores", Symbol { name = Simple "true"; _ } ->
      (* The generation of unsat core is supported only with the SAT
         solver Tableaux. *)
      if Stdlib.(Options.get_sat_solver () = Tableaux) then
        Options.set_unsat_core true
      else
        warning
          "%a The generation of unsat cores is not \
           supported for the current SAT solver. Please \
           choose the SAT solver Tableaux."
          Loc.report st_loc;
      st
    | ":produce-unsat-cores", Symbol { name = Simple "false"; _ } ->
      Options.set_unsat_core false; st
    | (":produce-models" | ":produce-unsat-cores" as name), _ ->
      print_wrn_opt ~name st_loc "boolean" value; st
    | ":verbosity", Symbol { name = Simple level; _ } ->
      begin
        match int_of_string_opt level with
        | Some i when i > 0 -> Options.set_verbose true
        | Some 0 -> Options.set_verbose false
        | None | Some _ ->
          print_wrn_opt ~name:":verbosity" st_loc "integer" value
      end;
      st
    | ":reproducible-resource-limit", Symbol { name = Simple level; _ } ->
      begin
        match int_of_string_opt level with
        | Some i when i > 0 -> Options.set_timelimit_per_goal true
        | Some 0 -> Options.set_timelimit_per_goal false
        | None | Some _ ->
          print_wrn_opt ~name:":reproducible-resource-limit" st_loc
            "nonnegative integer" value
      end;
      st
    | ":sat-solver", Symbol { name = Simple solver; _ } -> (
        if not (is_solver_ctx_empty (State.get solver_ctx_key st)) then (
          recoverable_error
            "error setting ':sat-solver', option value cannot be modified \
             after initialization";
          st
        ) else
          try
            let sat_solver =
              match solver with
              | "tableaux" -> Util.Tableaux
              | "tableaux_cdcl" -> Util.Tableaux_CDCL
              | "cdcl" | "satml" -> Util.CDCL
              | "cdcl_tableaux" | "satml_tableaux" | "default" ->
                Util.CDCL_Tableaux
              | _ -> raise Exit
            in
            Options.set_sat_solver sat_solver;
            let is_cdcl_tableaux =
              match sat_solver with CDCL_Tableaux -> true | _ -> false
            in
            Options.set_cdcl_tableaux_inst is_cdcl_tableaux;
            Options.set_cdcl_tableaux_th is_cdcl_tableaux;
            State.set sat_solver_key (make_sat ()) st
          with Exit ->
            recoverable_error
              "error setting ':sat-solver', invalid option value '%s'"
              solver;
            st
      )
    | (":global-declarations"
      | ":interactive-mode"
      | ":produce-assertions"
      | ":produce-assignments"
      | ":produce-proofs"
      | ":produce-unsat-assumptions"
      | ":print-success"
      | ":random-seed"), _
      ->
      unsupported_opt name; st
    (* Alt-Ergo custom options *)
    | ":profiling", Symbol { name = Simple level; _ } ->
      begin
        match float_of_string_opt level with
        | None -> print_wrn_opt ~name st_loc "nonnegative integer" value
        | Some i -> Options.set_profiling true i
      end; st
    | _ ->
      unsupported_opt name; st
  in

  let handle_get_info (st : State.t) (name: string) =
    let print_std =
      fun (type a) (pp :a Fmt.t) (a : a) ->
        Printer.print_std "(%s %a)" name pp a
    in
    let pp_reason_unknown st =
      let err () =
        recoverable_error "Invalid (get-info :reason-unknown)"
      in
      match State.get partial_model_key st with
      | None -> err ()
      | Some Model ((module SAT), sat) ->
        match SAT.get_unknown_reason sat with
        | None -> err ()
        | Some s ->
          print_std
            Format.pp_print_string
            (Frontend.unknown_reason_to_string s)
    in
    match name with
    | ":authors" ->
      print_std (fun fmt -> Fmt.pf fmt "%S") "Alt-Ergo developers"
    | ":error-behavior" ->
      let behavior =
        if Options.get_exit_on_error () then
          "immediate-exit"
        else
          "continued-execution"
      in
      print_std Fmt.string behavior
    | ":name" ->
      print_std (fun fmt -> Fmt.pf fmt "%S") "Alt-Ergo"
    | ":reason-unknown" ->
      pp_reason_unknown st
    | ":version" ->
      print_std Fmt.string Version._version
    | ":all-statistics" ->
      Printer.print_std "%t" Profiling.print_statistics;
      if not (Options.get_profiling ()) then
        warning "Profiling disactivated (try --profiling)"
    | ":assertion-stack-levels" ->
      unsupported_opt name
    | _ ->
      unsupported_opt name
  in

  let handle_stmt :
    Frontend.used_context -> State.t ->
    _ D_loop.Typer_Pipe.stmt -> State.t =
    let goal_cnt = ref 0 in
    fun all_context st td ->
      let file_loc = (State.get State.logic_file st).loc in
      let solver_ctx = State.get solver_ctx_key st in
      match td with
      (* When the next statement is a goal, the solver is called and provided
         the goal and the current context *)
      | { id; contents = (`Solve _ as contents); loc ; attrs } ->
        let l =
          solver_ctx.local @
          solver_ctx.global @
          solver_ctx.ctx
        in
        let id =
          match (State.get State.logic_file st).lang with
          | Some (Smtlib2 _) ->
            DStd.Id.mk DStd.Namespace.term @@
            "g_" ^ string_of_int (incr goal_cnt; !goal_cnt)
          | _ -> id
        in
        let name =
          match id.name with
          | Simple name -> name
          | _ ->
            let loc = DStd.Loc.loc file_loc loc in
            Fmt.failwith "%a: internal error: goal name should be simple"
              DStd.Loc.fmt loc
        in
        let contents =
          match contents with
          | `Solve (hyps, []) -> `Check hyps
          | `Solve ([], [t]) -> `Goal t
          | _ ->
            let loc = DStd.Loc.loc file_loc loc in
            Fmt.failwith "%a: internal error: unknown statement"
              DStd.Loc.fmt loc
        in
        let stmt = { Typer_Pipe.id; contents; loc ; attrs } in
        let cnf, is_thm =
          match D_cnf.make (State.get State.logic_file st).loc l stmt with
          | { Commands.st_decl = Query (_, _, kind); _ } as cnf :: hyps ->
            let is_thm =
              match kind with Ty.Thm | Sat -> true | _ -> false
            in
            List.rev (cnf :: hyps), is_thm
          | _ -> assert false
        in
        let partial_model =
          solve (State.get sat_solver_key st) all_context (cnf, name)
        in
        if is_thm
        then
          State.set solver_ctx_key (
            let solver_ctx = State.get solver_ctx_key st in
            { solver_ctx with global = []; local = [] }
          ) st
          |> State.set partial_model_key partial_model
        else
          State.set solver_ctx_key (
            let solver_ctx = State.get solver_ctx_key st in
            { solver_ctx with local = [] }
          ) st
          |> State.set partial_model_key partial_model

      | {contents = `Set_option
             { DStd.Term.term =
                 App ({ term = Symbol { name = Simple name; _ }; _ }, [value]);
               _
             }; loc = l; _ } ->
        let dloc_file = (State.get State.logic_file st).loc in
        let loc = DStd.Loc.(lexing_positions (loc dloc_file l)) in
        handle_option loc name value st

      | {contents = `Set_option _; _} ->
        recoverable_error "Invalid set-option";
        st

      | {contents = `Get_model; _ } ->
        if Options.get_interpretation () then
          match State.get partial_model_key st with
          | Some Model ((module SAT), partial_model) ->
            begin
              match SAT.get_model partial_model with
              | Some (lazy model) ->
                Models.output_concrete_model
                  (Options.Output.get_fmt_regular ()) model;
                st
              | _ ->
                (* TODO: is it reachable? *)
                st
            end
          | None ->
            (* TODO: add the location of the statement. *)
            recoverable_error "No model produced."; st
        else
          begin
            (* TODO: add the location of the statement. *)
            recoverable_error
              "Model generation disabled (try --produce-models)";
            st
          end

      | {contents = `Reset; _} ->
        st
        |> State.set partial_model_key None
        |> State.set solver_ctx_key empty_solver_ctx

      | {contents = `Exit; _} -> raise Exit

      | {contents = `Echo str; _} ->
        let new_str = String.concat "\"\"" (String.split_on_char '"' str) in
        Fmt.pf
          (Options.Output.get_fmt_regular ())
          "\"%s\"@."
          new_str;
        st

      | {contents = `Get_info kind; _ } ->
        handle_get_info st kind;
        st

      | _ ->
        (* TODO:
           - Separate statements that should be ignored from unsupported
             statements and throw exception or print a warning when an
             unsupported statement is encountered.
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
    let logic_file, st = mk_state filename in
    try
      Options.with_timelimit_if (not (Options.get_timelimit_per_goal ()))
      @@ fun () ->

      let builtin_dir = "<builtin>" in
      let theory_preludes =
        Options.get_theory_preludes ()
        |> List.map (fun theory ->
            let filename = Theories.filename theory in
            let content = Theories.content theory in
            State.mk_file builtin_dir (`Raw (filename, content)))
      in
      let preludes =
        theory_preludes @
        List.map (fun path ->
            let dir, source = State.split_input (`File path) in
            State.mk_file dir source) (Options.get_preludes ())
      in
      let g =
        Parser.parse_logic ~preludes logic_file
      in
      let st = State.set Typer.additional_builtins D_cnf.builtins st in
      let all_used_context = Frontend.init_all_used_context () in
      let finally = finally ~handle_exn in
      let st =
        let open Pipeline in
        let op_i ?name f = op ?name (fun st x -> f st x, ()) in
        run ~finally g st
          (fix
             (op ~name:"expand" Parser.expand)
             (op ~name:"debug_pre" debug_parsed_pipe
              @>|> op ~name:"typecheck" Typer_Pipe.typecheck
              @>|> op ~name:"debug_post" debug_typed_pipe
              @>|> op_i (handle_stmt all_used_context)
              @>>> _end))
      in
      State.flush st () |> ignore
    with exn ->
      let bt = Printexc.get_raw_backtrace () in
      ignore (handle_exn st bt exn)
  in

  let filename = get_file () in
  match get_frontend () with
  | "dolmen" -> d_fe filename
  | frontend -> ae_fe filename frontend
