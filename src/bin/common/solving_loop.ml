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
open D_loop

module DO = D_state_option
module Sy = Symbols
module O = Options

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

let enable_maxsmt b =
  if b then
    DStd.Extensions.Smtlib2.(enable maxsmt)
  else
    DStd.Extensions.Smtlib2.(disable maxsmt)

let cmd_on_modes st modes cmd =
  if O.get_input_format () = Some Options.Smtlib2 then begin
    let curr_mode = DO.Mode.get st in
    if not @@ (List.exists (Util.equal_mode curr_mode)) modes then
      Errors.forbidden_command curr_mode cmd
  end

(* Dolmen helpers *)

(** Adds the named terms of the statement [stmt] to the map accumulator [acc] *)
let add_if_named
    ~(acc : DStd.Expr.term Util.MS.t)
    (stmt : Typer_Pipe.typechecked D_loop.Typer_Pipe.stmt) =
  match stmt.contents with
  | `Defs [`Term_def ({name = Simple n; _}, id, _, _, t)] ->
    begin
      match DStd.Expr.Id.get_tag id DStd.Expr.Tags.named with
      | None -> acc
      | Some _ -> Util.MS.add n t acc
    end
  | _ -> (* Named terms are expected to be definitions with simple
            names. *)
    acc

type stmt = Typer_Pipe.typechecked D_loop.Typer_Pipe.stmt

(** Translates dolmen locs to Alt-Ergo's locs *)
let dl_to_ael dloc_file (compact_loc: DStd.Loc.t) =
  DStd.Loc.(lexing_positions (loc dloc_file compact_loc))

(* We currently use the full state of the solver as model. *)
type model = Model : 'a sat_module * 'a -> model

type solve_res =
  | Sat of model
  | Unknown of model option
  | Unsat of Explanation.t

let check_sat_status () =
  match Options.get_status () with
  | Status_Unsat ->
    recoverable_error
      "This file is known to be Unsat but Alt-Ergo return Sat";
  | _ -> ()

let check_unsat_status () =
  match Options.get_status () with
  | Status_Unsat ->
    recoverable_error
      "This file is known to be Sat but Alt-Ergo return Unsat";
  | _ -> ()

let print_solve_res loc goal_name r =
  let validity_mode =
    match Options.get_output_format () with
    | Smtlib2 -> false
    | Native | Why3 | Unknown _ -> true
  in
  let time = O.Time.value () in
  let steps = Steps.get_steps () in
  match r with
  | Sat _ ->
    Printer.print_status_sat ~validity_mode
      (Some loc) (Some time) (Some steps) (Some goal_name);
    check_sat_status ();
  | Unsat dep ->
    Printer.print_status_unsat ~validity_mode
      (Some loc) (Some time) (Some steps) (Some goal_name);
    if O.get_unsat_core() &&
       not (O.get_debug_unsat_core()) &&
       not (O.get_save_used_context())
    then
      Printer.print_fmt (Options.Output.get_fmt_regular ())
        "unsat-core:@,%a@."
        (Explanation.print_unsat_core ~tab:true) dep;
    check_unsat_status ()
  | Unknown _ ->
    Printer.print_status_unknown ~validity_mode
      (Some loc) (Some time) (Some steps) (Some goal_name);

exception StopProcessDecl

(** Returns the value bound to the key in the state in argument: if it does not
    exist, results default. *)
let state_get ~default key st =
  try State.get key st with State.Key_not_found _ -> default

let main () =
  let () = Dolmen_loop.Code.init [] in

  let solve (module SAT : Sat_solver_sig.S) all_context (cnf, goal_name) =
    let module FE = Frontend.Make (SAT) in
    if Options.get_debug_commands () then
      Printer.print_dbg "@[<v 2>goal %s:@ %a@]@."
        ~module_name:"Solving_loop" ~function_name:"solve"
        goal_name
        Fmt.(list ~sep:sp Commands.print) cnf;
    let used_context = Frontend.choose_used_context all_context ~goal_name in
    Signals_profiling.init_profiling ();
    try
      if Options.get_timelimit_per_goal() then
        begin
          Options.Time.start ();
          Options.Time.set_timeout (Options.get_timelimit ());
        end;
      SAT.reset_refs ();
      let ftdn_env = FE.init_env used_context in
      let hook_on_status status i =
        Frontend.print_status status i;
        match status with
        | Timeout _ when not (Options.get_timelimit_per_goal ()) ->
          exit_as_timeout ()
        | _ -> raise StopProcessDecl
      in
      let () =
        try
          List.iter
            (FE.process_decl ~hook_on_status ftdn_env)
            cnf
        with
        | StopProcessDecl -> ()
      in
      if Options.get_timelimit_per_goal() then
        Options.Time.unset_timeout ();
      if Options.get_profiling() then
        Profiling.print true
          (Steps.get_steps ())
          (Options.Output.get_fmt_diagnostic ());
      let partial_model = ftdn_env.sat_env in
      (* If the status of the SAT environment is inconsistent,
         we have to drop the partial model in order to prevent
         printing wrong model. *)
      match ftdn_env.FE.res with
      | `Sat ->
        begin
          let mdl = Model ((module SAT), partial_model) in
          if Options.(get_interpretation () && get_dump_models ()) then begin
            Fmt.pf (Options.Output.get_fmt_models ()) "%a@."
              FE.print_model partial_model
          end;
          Sat mdl
        end
      | `Unknown ->
        begin
          let mdl = Model ((module SAT), partial_model) in
          if Options.(get_interpretation () && get_dump_models ()) then begin
            let ur = SAT.get_unknown_reason partial_model in
            Printer.print_fmt (Options.Output.get_fmt_diagnostic ())
              "@[<v 0>Returned unknown reason = %a@]"
              Sat_solver_sig.pp_ae_unknown_reason_opt ur;
            Fmt.pf (Options.Output.get_fmt_models ()) "%a@."
              FE.print_model partial_model
          end;
          Unknown (Some mdl)
        end
      | `Unsat -> Unsat ftdn_env.expl
    with Util.Timeout ->
      (* It is still necessary to leave this catch here, because we may
         trigger this exception in between calls of the sat solver. *)
      if not (Options.get_timelimit_per_goal()) then exit_as_timeout ();
      Unknown None
  in

  let typed_loop all_context state td =
    if O.get_type_only () then state else begin
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
        Stdcompat.Seq.append theory_preludes @@
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
      if O.get_parse_only () then state else begin
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
    let sat_solver =
      let module SatCont =
        (val (Sat_solver.get_current ()) : Sat_solver_sig.SatContainer)
      in
      let module TH = (val Sat_solver.get_theory ~no_th:(O.get_no_theory ())) in
      (module SatCont.Make(TH) : Sat_solver_sig.S)
    in
    let state = {
      env = I.empty_env;
      solver_ctx = empty_solver_ctx;
      sat_solver;
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

  let partial_model_key: model option State.key =
    State.create_key ~pipe:"" "sat_state"
  in

  let named_terms: DStd.Expr.term Util.MS.t State.key =
    State.create_key ~pipe:"" "named_terms"
  in

  let incremental_depth : int State.key =
    State.create_key ~pipe:"" "is_incremental"
  in

  (* Set to true when a query is performed, states for the following SMT
     instructions that they are working on an environment in which some formulae
     have been decided and must be reverted back to the one before the check-sat
     before starting to assert again. *)
  let is_decision_env : bool State.key =
    State.create_key ~pipe:"" "is_decision_env"
  in

  (* Key used only in handle_stmt_pop_reinit, registers the commands executed
     to save them them if a push command is executed. *)
  let current_path_key : stmt list State.key =
    State.create_key ~pipe:"" "current_path"
  in

  (* Key used only in handle_stmt_pop_reinit, saves the commands executed
     when a push is executed and replays them when a pop is met. *)
  let pushed_paths_key : stmt list Vec.t State.key =
    State.create_key ~pipe:"" "pushed_paths"
  in

  (* Before each query, we push the current environment. This allows to keep a
     fresh one for the next assertions. *)
  let push_before_query st =
    assert (not (State.get is_decision_env st));
    let module Api = (val (DO.SatSolverModule.get st)) in
    Api.FE.push 1 Api.env;
    State.set is_decision_env true st
  in

  (* The pop corresponding to the previous push. It is applied everytime the
     mode goes from Sat/Unsat to Assert. *)
  let pop_if_post_query st =
    if State.get is_decision_env st then
      begin
        let module Api = (val (DO.SatSolverModule.get st)) in
        Api.FE.pop 1 Api.env;
        State.set is_decision_env false st
      end
    else
      st
  in

  let set_steps_bound i st =
    try DO.Steps.set i st with
      Invalid_argument _ -> (* Raised by Steps.set_steps_bound *)
      fatal_error
        "Error while setting steps bound to %i: current step = %i."
        i
        (Steps.get_steps ())
  in

  let debug_parsed_pipe st c =
    if State.get State.debug st then
      Format.eprintf "[logic][parsed][%a] @[<hov>%a@]@."
        Dolmen.Std.Loc.print_compact c.Dolmen.Std.Statement.loc
        Dolmen.Std.Statement.print c;
    if O.get_parse_only () then
      st, `Done ()
    else
      st, `Continue c
  in
  let debug_stmt stmt =
    Format.eprintf "[logic][typed][%a] @[<hov>%a@]@\n@."
      Dolmen.Std.Loc.print_compact stmt.Typer_Pipe.loc
      Typer_Pipe.print stmt
  in
  let debug_typed_pipe st stmts =
    if State.get State.debug st then
      List.iter debug_stmt stmts;
    if O.get_type_only () then
      st, `Done ()
    else
      st, `Continue stmts
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
  let set_mode ?model mode st =
    let st = DO.Mode.set mode st in
    match mode with
    | Sat ->
      State.set partial_model_key model st
    | _ ->
      State.set partial_model_key None st
  in
  let set_partial_model_and_mode solve_res st =
    match solve_res with
    | Unsat _ ->
      set_mode Unsat st
    | Unknown None ->
      set_mode Sat st
    | Unknown (Some model)
    | Sat model ->
      set_mode Sat ~model st
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
      ?(solver_ctx = empty_solver_ctx) path =
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
      | Some Smtlib2 -> Some (Dl.Logic.Smtlib2 `Poly)
      | None ->
        (* Dolmen auto-detects .smt2 files as adhering to the SMT-LIB standard,
           but we want to allow the polymorphic extensions instead. *)
        let filename =
          if Filename.check_suffix path ".zip" then
            Filename.chop_extension path
          else
            path
        in
        if Filename.check_suffix filename ".smt2" then
          Some (Dl.Logic.Smtlib2 `Poly)
        else
          None
      | Some (Why3 | Unknown _) -> None
    in
    let source =
      if Filename.check_suffix path ".zip" then (
        Filename.(chop_extension path |> extension) |> set_output_format;
        let content = AltErgoLib.My_zip.extract_zip_file path in
        `Raw (Filename.chop_extension filename, content))
      else
        let is_stdin = String.equal path "" in
        let is_incremental =
          match lang with
          | Some (Dl.Logic.Smtlib2 _) | None -> true
          | _ -> false
        in
        if is_stdin then (
          if is_incremental then (
            set_output_format ".smt2";
            `Stdin
          ) else (
            `Raw (filename, read_all stdin)
          )
        ) else (
          Filename.extension path |> set_output_format;
          let cin = open_in path in
          let content = read_all cin in
          close_in cin;
          `Raw (filename, content)
        )
    in
    let logic_file =
      State.mk_file ?lang ~loc:(Dolmen.Std.Loc.mk_file path) dir source
    in
    let response_file = State.mk_file dir (`Raw ("", "")) in
    logic_file,
    State.empty
    |> State.set solver_ctx_key solver_ctx
    |> State.set partial_model_key None
    |> State.set named_terms Util.MS.empty
    |> State.set incremental_depth 0
    |> State.set is_decision_env false
    |> DO.init
    |> State.init ~debug ~report_style ~reports ~max_warn ~time_limit
      ~size_limit ~response_file
    |> Parser.init
    |> Typer.init
      ~additional_builtins:D_cnf.builtins
      ~extension_builtins:[Typer.Ext.bv2nat]
    |> Typer_Pipe.init ~type_check
  in

  (* Initializing hooks in the mode handler.
     When we perform a check-sat, the environment we are working on is specific
     to the Sat or Unsat mode we end up in. If we start asserting again, we must
     do it in the previous environment.
  *)
  let init_full_incremental_hooks () =
    DO.Mode.reset_hooks ();
    DO.Mode.add_hook
      (fun _ ~old:_ ~new_ st ->
         match new_ with
         | Assert -> pop_if_post_query st
         | _ -> st
      )
  in
  let print_wrn_opt ~name loc ty value =
    warning
      "%a The option %s expects a %s, got %a"
      Loc.report loc name ty DStd.Term.print value
  in

  let set_sat_solver sat st =
    let optim = DO.Optimize.get st in
    match sat with
    | Util.Tableaux | Tableaux_CDCL when optim ->
      warning
        "Sat-solver %a is incompatible with optimization: ignoring command."
        Util.pp_sat_solver
        sat;
      st
    | Tableaux | Tableaux_CDCL | CDCL | CDCL_Tableaux ->
      O.set_sat_solver sat;
      (* `make_sat` returns the sat solver corresponding to the new sat_solver
         option. *)
      DO.SatSolver.set sat st
  in

  let set_optimize optim st =
    let sat = DO.SatSolver.get st in
    match sat with
    | Util.Tableaux | Tableaux_CDCL when optim ->
      warning
        "Sat-solver %a is incompatible with optimization: ignoring command."
        Util.pp_sat_solver
        sat;
      st
    | Tableaux | Tableaux_CDCL | CDCL | CDCL_Tableaux ->
      enable_maxsmt optim;
      DO.Optimize.set optim st
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
            let is_cdcl_tableaux =
              match sat_solver with CDCL_Tableaux -> true | _ -> false
            in
            Options.set_cdcl_tableaux_inst is_cdcl_tableaux;
            Options.set_cdcl_tableaux_th is_cdcl_tableaux;
            set_sat_solver sat_solver st
          with Exit ->
            recoverable_error
              "error setting ':sat-solver', invalid option value '%s'"
              solver;
            st
      )
    | ":produce-assignments",  Symbol { name = Simple b; _ } ->
      begin
        match bool_of_string_opt b with
        | None ->
          print_wrn_opt ~name:":verbosity" st_loc "boolean" value;
          st
        | Some b -> DO.ProduceAssignment.set b st
      end
    | (":global-declarations"
      | ":interactive-mode"
      | ":produce-assertions"
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
    | ":optimization", Symbol { name = Simple b; _} ->
      begin
        match bool_of_string_opt b with
        | None -> print_wrn_opt ~name st_loc "bool" value; st
        | Some b ->
          set_optimize b st
      end
    | ":steps-bound", Symbol { name = Simple level; _ } ->
      begin
        match int_of_string_opt level with
        | None -> print_wrn_opt ~name st_loc "integer" value; st
        | Some i -> set_steps_bound i st
      end
    | _ ->
      unsupported_opt name; st
  in

  let handle_optimize_stmt ~is_max loc expr st =
    let st = DO.Mode.set Assert st in
    let module Api = (val (DO.SatSolverModule.get st)) in
    if State.get incremental_depth st > 0 then
      warning "Optimization constraints in presence of push \
               and pop statements are not correctly processed.";
    let () =
      if not @@ D_cnf.is_pure_term expr then
        begin
          recoverable_error
            "the expression %a is not a valid objective function. \
             Only terms without let bindings or ite subterms can be optimized."
            Expr.print expr
        end
      else
        Api.FE.optimize ~loc (expr, is_max) Api.env
    in st
  in

  let handle_get_objectives (_args : DStd.Expr.Term.t list) st =
    if Options.get_interpretation () then
      match State.get partial_model_key st with
      | Some Model ((module SAT), partial_model) ->
        let objectives = SAT.get_objectives partial_model in
        begin
          match objectives with
          | Some o ->
            if not @@ Objective.Model.has_no_limit o then
              warning "Some objectives cannot be fulfilled";
            Objective.Model.pp (Options.Output.get_fmt_regular ()) o
          | None ->
            recoverable_error "No objective generated"
        end
      | None ->
        recoverable_error
          "Model generation is disabled (try --produce-models)"
  in

  let handle_custom_statement loc id args st =
    let args = List.map Dolmen_type.Core.Smtlib2.sexpr_as_term args in
    let logic_file = State.get State.logic_file st in
    let st, terms = Typer.terms st ~input:(`Logic logic_file) ~loc args in
    let loc =
      let dloc_file = (State.get State.logic_file st).loc in
      dl_to_ael dloc_file loc
    in
    match id, terms.ret with
    | Dolmen.Std.Id.{name = Simple ("minimize" as name_base); _}, [term] ->
      cmd_on_modes st [Assert] "minimize";
      let expr =
        D_cnf.mk_expr
          ~loc
          ~name_base
          ~toplevel:true
          ~decl_kind:Expr.Dobjective
          term
      in
      handle_optimize_stmt ~is_max:false loc expr st
    | Dolmen.Std.Id.{name = Simple ("maximize" as name_base); _}, [term] ->
      cmd_on_modes st [Assert] "maximize";
      let expr =
        D_cnf.mk_expr
          ~loc
          ~name_base
          ~toplevel:true
          ~decl_kind:Expr.Dobjective
          term
      in
      handle_optimize_stmt ~is_max:true loc expr st
    | Dolmen.Std.Id.{name = Simple "get-objectives"; _}, terms ->
      cmd_on_modes st [Sat] "get-objectives";
      handle_get_objectives terms st;
      st
    | Dolmen.Std.Id.{name = Simple (("minimize" | "maximize") as ext); _}, _ ->
      recoverable_error
        "Statement %s only expects 1 argument (%i given)"
        ext
        (List.length args);
      st
    | n, _ ->
      recoverable_error
        "Unknown statement %a."
        Dolmen.Std.Id.print
        n;
      st
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
        | Some ur ->
          print_std Sat_solver_sig.pp_smt_unknown_reason ur
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
      Printer.print_std "%t" Profiling.print_statistics
    | ":assertion-stack-levels" ->
      unsupported_opt name
    | _ ->
      unsupported_opt name
  in

  (* Fetches the term value in the current model. *)
  let evaluate_term get_value name term =
    (* There are two ways to evaluate a term:
       - if its name is registered in the environment, get its value;
       - if not, check if the formula is in the environment.
    *)
    let simple_form =
      Expr.mk_term
        (Sy.name name)
        []
        (D_cnf.dty_to_ty term.DStd.Expr.term_ty)
    in
    match get_value simple_form with
    | Some v -> Fmt.to_to_string Expr.print v
    | None -> "unknown"
  in

  let print_terms_assignments =
    Fmt.list
      ~sep:Fmt.cut
      (fun fmt (name, v) -> Fmt.pf fmt "(%s %s)" name v)
  in

  let handle_get_assignment ~get_value st =
    let assignments =
      Util.MS.fold
        (fun name term acc ->
           if DStd.Expr.Ty.equal term.DStd.Expr.term_ty DStd.Expr.Ty.bool then
             (name, evaluate_term get_value name term) :: acc
           else
             acc
        )
        (State.get named_terms st)
        []
    in
    Printer.print_std
      "(@[<v 0>%a@])@,"
      print_terms_assignments
      assignments
  in

  (* Copied from D_cnf, this treats the `Hyp case. *)
  let assume_axiom st name t loc attrs : unit =
    let module Api = (val (DO.SatSolverModule.get st)) in
    let dloc_file = (State.get State.logic_file st).loc in
    let dloc = DStd.Loc.loc dloc_file loc in
    let aloc = DStd.Loc.lexing_positions dloc in
    (* Dolmen adds information about theory extensions and case splits in the
       [attrs] field of the parsed statements. [attrs] can be arbitrary terms,
       where the information we care about is encoded as a [Colon]-list of
       symbols.

       The few helper functions below are used to extract the information from
       the [attrs]. More specifically:

       - "case split" statements have the [DStd.Id.case_split] symbol as an
          attribute

       - Theory elements have a 3-length list of symbols as an attribute, of
          the form [theory_decl; name; extends], where [theory_decl] is the
          symbol [DStd.Id.theory_decl] and [name] and [extends] are the theory
          extension name and the base theory name, respectively.
    *)
    let rec symbols = function
      | DStd.Term. { term = Colon ({ term = Symbol sy; _ }, xs); _ } ->
        Option.bind (symbols xs) @@ fun sys ->
        Some (sy :: sys)
      | { term = Symbol sy; _ } -> Some [sy]
      | _ -> None
    in
    let sy_attrs = List.filter_map symbols attrs in
    let is_case_split =
      let is_case_split = function
        | [ sy ] when DStd.Id.(equal sy case_split) -> true
        | _ -> false
      in
      List.exists is_case_split sy_attrs
    in
    let theory =
      let theory =
        let open DStd.Id in
        function
        | [ td; name; extends] when DStd.Id.(equal td theory_decl) ->
          let name = match name.name with
            | Simple name -> name
            | _ ->
              Fmt.failwith
                "Internal error: invalid theory extension: %a"
                print name
          in
          let extends = match extends.name with
            | Simple name ->
              begin match Util.th_ext_of_string name with
                | Some extends -> extends
                | None ->
                  Errors.typing_error (ThExtError name) aloc
              end
            | _ ->
              Fmt.failwith
                "Internal error: invalid base theory name: %a"
                print extends
          in
          Some (name, extends)
        | _ -> None
      in
      match List.filter_map theory sy_attrs with
      | [] -> None
      | [name, extends] -> Some (name, extends)
      | _ ->
        Fmt.failwith
          "%a: Internal error: multiple theories."
          DStd.Loc.fmt dloc
    in
    let st_loc = dl_to_ael dloc_file loc in
    match theory with
    | Some (th_name, extends) ->
      let axiom_kind =
        if is_case_split then Util.Default else Util.Propagator
      in
      let e = D_cnf.make_form name t st_loc ~decl_kind:Expr.Dtheory in
      let th_elt = {
        Expr.th_name;
        axiom_kind;
        extends;
        ax_form = e;
        ax_name = name;
      } in
      Api.FE.th_assume ~loc:st_loc th_elt Api.env
    | None ->
      let e = D_cnf.make_form name t st_loc ~decl_kind:Expr.Daxiom in
      Api.FE.assume ~loc:st_loc (name, e, true) Api.env
  in

  (* Push the current environment and performs the query.
     If an assertion is performed, we have to pop it back. This is handled by
     the hook on D_state_option.Mode. *)
  let handle_query st id loc attrs contents =
    let module Api = (val (DO.SatSolverModule.get st)) in
    let st_loc =
      let file_loc = (State.get State.logic_file st).loc in
      dl_to_ael file_loc loc
    in
    let name =
      match id.DStd.Id.name with
      | Simple name -> name
      | Indexed _ | Qualified _ -> assert false
    in
    (* First, we check the environment if it already concluded. *)
    let solve_res =
      match Api.env.res with
      | `Unsat -> Unsat Api.env.expl
      | `Sat
      | `Unknown ->
        (* The environment did not conclude yet, or concluded with SAT. We
           add additional constraints which may change this result. *)
        begin
          (* Preprocessing query. *)
          let goal_sort =
            match contents with
            | `Goal _ -> Ty.Thm
            | `Check _ -> Ty.Sat
          in
          let hyps, t =
            match contents with
            | `Goal t ->
              D_cnf.pp_query t
            | `Check hyps ->
              D_cnf.pp_query ~hyps (DStd.Expr.Term.(of_cst Const._false))
          in
          let () =
            List.iter (
              fun t ->
                let name = Ty.fresh_hypothesis_name goal_sort in
                assume_axiom st name t loc attrs
            ) hyps
          in
          let e = D_cnf.make_form "" t st_loc ~decl_kind:Expr.Dgoal in
          (* Performing the query. *)
          Api.FE.query ~loc:st_loc (name, e, goal_sort) Api.env;
          (* Treatment of the result. *)
          let partial_model = Api.env.sat_env in
          (* If the status of the SAT environment is inconsistent,
             we have to drop the partial model in order to prevent
             printing wrong model. *)
          match Api.env.res with
          | `Sat ->
            begin
              let mdl = Model ((module Api.SAT), partial_model) in
              let () =
                if Options.(get_interpretation () && get_dump_models ()) then
                  Api.FE.print_model
                    (Options.Output.get_fmt_models ())
                    partial_model
              in
              Sat mdl
            end
          | `Unknown ->
            begin
              let mdl = Model ((module Api.SAT), partial_model) in
              if Options.(get_interpretation () && get_dump_models ()) then
                begin
                  let ur = Api.SAT.get_unknown_reason partial_model in
                  Printer.print_fmt (Options.Output.get_fmt_diagnostic ())
                    "@[<v 0>Returned unknown reason = %a@]"
                    Sat_solver_sig.pp_ae_unknown_reason_opt ur;
                  Api.FE.print_model
                    (Options.Output.get_fmt_models ())
                    partial_model
                end;
              Unknown (Some mdl)
            end
          | `Unsat -> Unsat Api.env.expl
        end
    in
    (* Prints the result. *)
    print_solve_res st_loc name solve_res;
    (* Updates the dolmen state. *)
    set_partial_model_and_mode solve_res st
  in

  let handle_solve =
    let goal_cnt = ref 0 in
    fun st id contents loc attrs ->
      let module Api = (val DO.SatSolverModule.get st) in
      let file_loc = (State.get State.logic_file st).loc in
      let id =
        match (State.get State.logic_file st).lang with
        | Some (Smtlib2 _) ->
          DStd.Id.mk DStd.Namespace.term @@
          "g_" ^ string_of_int (incr goal_cnt; !goal_cnt)
        | _ -> id
      in
      let contents =
        match contents with
        | `Solve (hyps, []) -> `Check hyps
        | `Solve ([], [t]) -> `Goal t
        | _ ->
          let loc = DStd.Loc.loc file_loc loc in
          fatal_error "%a: internal error: unknown statement"
            DStd.Loc.fmt loc
      in
      (* Performing the query *)
      handle_query st id loc attrs contents
  in

  (* TODO: reset options to their initial value. *)
  let handle_reset st =
    st
    |> State.set partial_model_key None
    |> State.set solver_ctx_key empty_solver_ctx
    |> State.set is_decision_env false
    |> DO.Mode.clear
    |> DO.Optimize.clear
    |> DO.ProduceAssignment.clear
    |> DO.init
    |> State.set named_terms Util.MS.empty
  in

  let handle_stmt_full_incremental :
    Frontend.used_context ->
    State.t ->
    [< Typer_Pipe.typechecked | `Check of 'a ] D_loop.Typer_Pipe.stmt ->
    State.t =
    fun _all_context st td ->
      let file_loc = (State.get State.logic_file st).loc in
      match td with
      (* Set logic *)
      | { contents = `Set_logic _; _} ->
        cmd_on_modes st [Start] "set-logic";
        DO.Mode.set Util.Assert st
      (* Goal definition *)
      | {
        id; loc; attrs;
        contents = (`Goal _) as contents;
        implicit = _;
      } ->
        (* In the non imperative mode, the Solve instruction is handled
           differently (i.e. no pop/push). *)
        assert (not (Options.get_imperative_mode ()));
        cmd_on_modes st [Assert; Sat; Unsat] "goal";
        let st = pop_if_post_query st in
        (* Pushing the environment once. This allows to keep a trace of the old
           environment in case we want to assert afterwards.
           The `pop` instruction is handled by the hook on the mode: when we
           assert anything, we must make sure to go back to `Assert` mode. *)
        let st = push_before_query st in
        handle_query st id loc attrs contents

      (* Axiom definitions *)
      | { id = DStd.Id.{name = Simple name; _}; contents = `Hyp t; loc; attrs;
          implicit=_ } ->
        let st = DO.Mode.set Util.Assert st in
        assume_axiom st name t loc attrs;
        st

      | { contents = `Defs defs; loc; _ } ->
        let module Api = (val (DO.SatSolverModule.get st)) in
        let st = DO.Mode.set Util.Assert st in
        let loc = dl_to_ael file_loc loc in
        let defs = D_cnf.make_defs defs loc in
        let () =
          List.iter
            (function
              | `Assume (name, e) -> Api.FE.assume ~loc (name, e, true) Api.env
              | `PredDef (e, name) -> Api.FE.pred_def ~loc (name, e) Api.env
            )
            defs
        in
        st

      | {contents = `Decls l; loc; _} ->
        let st = DO.Mode.set Util.Assert st in
        let decls = D_cnf.make_decls l in
        let module Api = (val DO.SatSolverModule.get st) in
        let loc = dl_to_ael file_loc loc in
        List.iter (fun decl -> Api.FE.declare ~loc decl Api.env) decls;
        st

      (* When the next statement is a goal, the solver is called and provided
         the goal and the current context *)
      | { id; contents = (`Solve _ as contents); loc ; attrs; implicit=_ } ->
        (* In the non imperative mode, the Solve instruction is handled
           differently (i.e. no pop/push). *)
        assert (not (Options.get_imperative_mode ()));
        cmd_on_modes st [Assert; Unsat; Sat] "check-sat";
        let st = pop_if_post_query st in
        (* Pushing the environment once. This allows to keep a trace of the old
           environment in case we want to assert afterwards.
           The `pop` instruction is handled by the hook on the mode: when we
           assert anything, we must make sure to go back to `Assert` mode. *)
        let st = push_before_query st in
        handle_solve st id contents loc attrs

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
        cmd_on_modes st [Sat] "get-model";
        if Options.get_interpretation () then
          let () = match State.get partial_model_key st with
            | Some (Model ((module SAT), env)) ->
              let module FE = Frontend.Make (SAT) in
              Fmt.pf (Options.Output.get_fmt_regular ()) "%a@."
                FE.print_model env
            | None ->
              (* TODO: add the location of the statement. *)
              recoverable_error "No model produced."
          in
          st
        else
          begin
            (* TODO: add the location of the statement. *)
            recoverable_error
              "Model generation disabled (try --produce-models)";
            st
          end

      | {contents = `Reset; _} ->
        let () = Steps.reset_steps () in
        handle_reset st

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

      | {contents = `Get_assignment; _} ->
        begin
          cmd_on_modes st [Sat] "get-assignment";
          match State.get partial_model_key st with
          | Some Model ((module SAT), partial_model) ->
            if DO.ProduceAssignment.get st then
              handle_get_assignment
                ~get_value:(SAT.get_value partial_model)
                st
            else
              recoverable_error
                "Produce assignments disabled; \
                 add (set-option :produce-assignments true)";
            st
          | None ->
            (* TODO: add the location of the statement. *)
            recoverable_error
              "No model produced, cannot execute get-assignment.";
            st
        end

      | {contents = `Other (custom, args); loc; _} ->
        handle_custom_statement loc custom args st

      | {contents = `Pop n; loc; _} ->
        let module Api = (val DO.SatSolverModule.get st) in
        let dloc_file = (State.get State.logic_file st).loc in
        Api.FE.pop ~loc:(dl_to_ael dloc_file loc) n Api.env;
        st
        |> State.set incremental_depth (State.get incremental_depth st - n)
        |> set_mode Assert

      | {contents = `Push n; loc; _} ->
        let module Api = (val DO.SatSolverModule.get st) in
        let dloc_file = (State.get State.logic_file st).loc in
        Api.FE.push ~loc:(dl_to_ael dloc_file loc) n Api.env;
        st
        |> State.set incremental_depth (State.get incremental_depth st + n)
        |> set_mode Assert

      | td ->
        Printer.print_dbg ~header:true
          "Ignoring statement: %a" Typer_Pipe.print td;
        st
  in

  (* Handle each statement one after the other.
     Still experimental due to push & pop issues. *)
  let handle_stmts_full_incremental all_context st l =
    let rec aux named_map st = function
      | [] -> State.set named_terms named_map st
      | stmt :: tl ->
        let st = handle_stmt_full_incremental all_context st stmt in
        let named_map = add_if_named ~acc:named_map stmt in
        aux named_map st tl
    in
    aux (State.get named_terms st) st l
  in

  let get_current_path = state_get ~default:[] current_path_key in

  let get_pushed_paths =
    state_get ~default:(Vec.create ~dummy:[]) pushed_paths_key
  in

  (* Same as handle_stmts_full_incremental, but removes pops and pushes.
     Instead, every command that perform an effect on the environment
     (definitions, assertion, resets, set option, ...) are stored in a list of
     commands. When a (push n) is performed, this list is stored n times in a
     Vec. When a pop m occurs, we reset the analysis, the Vec is popped m times
     and the list of commands is replayed before continuing the analysis.
     /!\ Pop do not reset options, so there may be inconstencies between a first
     execution and a reinitialized one. The handle_reset function should handle
     this, but it is not the case yet. *)
  let handle_stmt_pop_reinit all_context st l =

    let has_timeout st =
      let module Api = (val DO.SatSolverModule.get st) in
      match Api.SAT.get_unknown_reason Api.env.sat_env with
      | Some (Timeout _) -> true
      | _ -> false
    in

    (* Pushes n times the current path. *)
    let push n st =
      let current_path = get_current_path st in
      let pushed_paths = get_pushed_paths st in
      for _ = 0 to n - 1 do
        Vec.push pushed_paths current_path
      done
    in

    (* Pops n times the current path and calls [replay] on the
       list of instruction returned. *)
    let pop n st replay =
      let pushed_paths = get_pushed_paths st in
      let rec pop_until until res =
        if until = 0 then
          res
        else
          pop_until (until - 1) (Vec.pop pushed_paths)
      in
      let rev_prefix = pop_until (n - 1) (Vec.pop pushed_paths) in
      let st = handle_reset st in
      (* Part of the reset, the current path must be reinitialized as well. *)
      let st = State.set current_path_key [] st in
      replay st (List.rev rev_prefix)
    in

    (* Before each query, we push the current environment. This allows to keep a
       fresh one for the next assertions. *)
    let push_before_query st =
      assert (not (State.get is_decision_env st));
      push 1 st;
      State.set is_decision_env true st
    in
    (* The pop corresponding to the previous push. It must be applied everytime
       the mode goes from Sat/Unsat to Assert. *)
    let rec pop_if_post_query st =
      if State.get is_decision_env st
      then pop 1 st (aux Util.MS.empty)
      else st
    and aux named_map st = function
      | [] -> State.set named_terms named_map st
      | (stmt: stmt) :: tl ->
        begin
          let current_path = get_current_path st in
          match stmt with
          | {contents = `Push n; _} ->
            push n st;
            let st = set_mode Assert st in
            aux named_map st tl
          | {contents = `Pop n; _} ->
            let st = set_mode Assert st in
            pop n st begin fun st prefix ->
              let st = aux Util.MS.empty st prefix in
              aux (State.get named_terms st) st tl
            end
          | {
            id; loc; attrs;
            contents = (`Goal _) as contents;
            implicit = _;
          } ->
            cmd_on_modes st [Assert; Sat; Unsat] "goal";
            let st = pop_if_post_query st in
            let st = push_before_query st in
            let st = handle_query st id loc attrs contents in
            let () =
              if has_timeout st then
                if Options.get_timelimit_per_goal ()
                then begin
                  Options.Time.start ();
                  Options.Time.set_timeout (Options.get_timelimit ());
                end
                else exit_as_timeout ()
            in
            st
          | {
            id; contents = (`Solve _ as contents); loc ; attrs; implicit=_
          } ->
            cmd_on_modes st [Assert; Unsat; Sat] "check-sat";
            let st = pop_if_post_query st in
            let st = push_before_query st in
            let st = handle_solve st id contents loc attrs in
            let () =
              if has_timeout st then
                if Options.get_timelimit_per_goal ()
                then begin
                  Options.Time.start ();
                  Options.Time.set_timeout (Options.get_timelimit ());
                end
                else exit_as_timeout ()
            in
            st
          | {contents; _ } ->
            let st =
              let new_current_path =
                match contents with
                (* Treated above *)
                | `Goal _
                | `Push _
                | `Pop _
                | `Solve (_, _) -> assert false
                (* Statemets to keep *)
                | `Clause _
                | `Decls _
                | `Defs _
                | `Exit (* This case should not happen.*)
                | `Hyp _
                | `Reset
                | `Reset_assertions
                | `Set_info _
                | `Set_logic _
                | `Set_option _ -> stmt :: current_path
                (* Statements to remove *)
                | `Echo _
                | `Get_assertions
                | `Get_info _
                | `Get_model
                | `Get_option _
                | `Get_proof
                | `Get_unsat_core
                | `Get_value _
                | `Get_assignment
                | `Get_unsat_assumptions -> current_path
                (* Custom statement *)
                | `Other (custom, _) ->
                  begin
                    match custom with
                    | {name = Simple ("minimize" | "maximize"); _} ->
                      stmt :: current_path
                    | _ -> current_path
                  end
              in
              State.set current_path_key new_current_path st
            in
            let st = handle_stmt_full_incremental all_context st stmt in
            let named_map = add_if_named ~acc:named_map stmt in
            aux named_map st tl
        end
    in
    DO.Mode.reset_hooks ();
    DO.Mode.add_hook
      (fun _ ~old:_ ~new_ st ->
         match new_ with
         | Assert -> pop_if_post_query st
         | _ -> st
      );
    aux (State.get named_terms st) st l
  in
  let handle_stmts all_context st l =
    begin
      if Options.get_imperative_mode ()
      then
        let () = init_full_incremental_hooks () in
        handle_stmts_full_incremental
      else handle_stmt_pop_reinit
    end all_context st l
  in
  let d_fe filename =
    let logic_file, st = mk_state filename in
    let () =
      (* Activating maxsmt if the optimize option is ON. *)
      enable_maxsmt (O.get_optimize ())
    in
    try
      Options.with_timelimit_if (not (Options.get_timelimit_per_goal ()))
      @@ fun () ->
      Options.Time.start ();
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
              @>|> op_i (handle_stmts all_used_context)
              @>>> _end))
      in
      State.flush st () |> ignore
    with exn ->
      let bt = Printexc.get_raw_backtrace () in
      ignore (handle_exn st bt exn)
  in

  let filename = O.get_file () in
  match O.get_frontend () with
  | "dolmen" -> d_fe filename
  | frontend -> ae_fe filename frontend
