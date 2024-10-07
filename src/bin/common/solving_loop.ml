(**************************************************************************)
(*                                                                        *)
(*     Alt-Ergo: The SMT Solver For Software Verification                 *)
(*     Copyright (C) --- OCamlPro SAS                                     *)
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
          | Smtlib2 _ -> Printer.print_smtlib_err "%s" msg
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
    | Smtlib2 _ -> Printer.print_std "unsupported"
    | _ -> ()
  in
  warning "unsupported option %s" opt

let on_strict_mode b =
  (* For now, strict mode only disables optimization. *)
  if b then
    DStd.Extensions.Smtlib2.(disable maxsmt)
  else
    DStd.Extensions.Smtlib2.(enable maxsmt)

let cmd_on_modes st modes cmd =
  match O.get_input_format () with
  | Some Smtlib2 _ ->
    let curr_mode = DO.Mode.get st in
    if not @@ (List.exists (Util.equal_mode curr_mode)) modes then
      Errors.forbidden_command curr_mode cmd
  | _ -> ()

(* Dolmen util *)

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

(* We currently use the full state of the solver as model. *)
type model = Model : 'a sat_module * 'a -> model

type solve_res =
  | Sat of model
  | Unknown of model option
  | Unsat

exception StopProcessDecl

let process_source ?selector_inst ~print_status src =
  let () = Dolmen_loop.Code.init [] in

  let hook_on_status status i =
    print_status status i;
    match (status : Frontend.status) with
    | Timeout _ when not (Options.get_timelimit_per_goal ()) ->
      exit_as_timeout ()
    | _ -> raise StopProcessDecl
  in

  let solve (module SAT : Sat_solver_sig.S)
      all_context (cnf, goal_name) =
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
      let ftdn_env = FE.init_env ?selector_inst used_context in
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
      | `Unsat -> Unsat
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
    | Unsat ->
      set_mode Unsat st
    | Unknown None ->
      set_mode Sat st
    | Unknown (Some model)
    | Sat model ->
      set_mode Sat ~model st
  in
  let set_output_format fmt =
    match fmt with
    | Dl.Logic.Alt_ergo ->
      Options.set_output_format Native
    | Dl.Logic.(Smtlib2 version) ->
      Options.set_output_format (Smtlib2 version)
    | _ -> ()
  in
  let infer_output_format src =
    if Options.get_infer_output_format () then
      match src with
      | `File filename
      | `Raw (filename, _) ->
        begin match Filename.extension filename with
          | ".ae" -> set_output_format Dl.Logic.Alt_ergo
          | ".smt2" -> set_output_format Dl.Logic.(Smtlib2 `Latest)
          | ".psmt2" -> set_output_format Dl.Logic.(Smtlib2 `Poly)
          | ext ->
            warning "cannot infer output format from the extension '%s'" ext
        end
      | `Stdin -> ()
  in
  (* Prepare the input source for Dolmen from an input source for Alt-Ergo. *)
  let mk_files src =
    let lang =
      match Options.get_input_format () with
      | Some Native -> Some Dl.Logic.Alt_ergo
      | Some Smtlib2 version -> Some (Dl.Logic.Smtlib2 version)
      | Some (Why3 | Unknown _) | None -> None
    in
    let src =
      match src with
      | `File path when Filename.check_suffix path ".zip" ->
        let content = AltErgoLib.My_zip.extract_zip_file path in
        `Raw (Filename.(chop_extension path |> basename), content)
      | `File _ | `Raw _ | `Stdin -> src
    in
    infer_output_format src;
    let input_file = State.mk_file ?lang "" src in
    let response_file = State.mk_file "" (`Raw ("", "")) in
    input_file, response_file
  in
  let mk_state ?(debug = false) ?(report_style = State.Contextual)
      ?(max_warn = max_int) ?(time_limit = Float.infinity)
      ?(size_limit = Float.infinity) ?(type_check = true)
      ?(solver_ctx = empty_solver_ctx) src =
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
    let logic_file, response_file = mk_files src in
    logic_file,
    State.empty
    |> State.set solver_ctx_key solver_ctx
    |> State.set partial_model_key None
    |> State.set named_terms Util.MS.empty
    |> DO.init
    |> State.init ~debug ~report_style ~reports ~max_warn ~time_limit
      ~size_limit ~response_file
    |> Parser.init
    |> Typer.init
      ~additional_builtins:D_cnf.builtins
      ~extension_builtins:[Typer.Ext.bv2nat]
    |> Typer_Pipe.init ~type_check
  in

  let print_wrn_opt ~name loc ty value =
    warning
      "%a The option %s expects a %s, got %a"
      Loc.report loc name ty DStd.Term.print value
  in

  let set_sat_solver sat st =
    O.set_sat_solver sat;
    (* `make_sat` returns the sat solver corresponding to the new sat_solver
       option. *)
    DO.SatSolver.set sat st
  in

  let set_strict_mode strict_mode st =
    on_strict_mode strict_mode;
    DO.StrictMode.set strict_mode st
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
        if Sys.unix then
          match int_of_string_opt level with
          | Some i when i > 0 ->
            Options.set_timelimit_per_goal true;
            Options.set_timelimit (float_of_int i /. 1000.)
          | Some 0 ->
            Options.set_timelimit_per_goal false;
            Options.set_timelimit 0.
          | None | Some _ ->
            print_wrn_opt ~name:":reproducible-resource-limit" st_loc
              "nonnegative integer" value
        else
          warning "%a :reproducible-resource-limit is only supported on Unix"
            Loc.report st_loc
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
    | ":strict-mode", Symbol { name = Simple b; _} ->
      begin
        match bool_of_string_opt b with
        | None -> print_wrn_opt ~name st_loc "bool" value; st
        | Some b -> set_strict_mode b st
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

  let handle_optimize_stmt ~is_max loc id (term : DStd.Expr.Term.t) st =
    let module Sat = (val DO.SatSolverModule.get st) in
    if not Sat.supports_optimization then (
      recoverable_error "the selected solver does not support optimization";
      st
    ) else
      let contents = `Optimize (term, is_max) in
      let stmt =
        { Typer_Pipe.id; contents; loc; attrs = []; implicit = false }
      in
      let cnf =
        D_cnf.make (State.get State.logic_file st).loc
          (State.get solver_ctx_key st).ctx stmt
      in
      State.set solver_ctx_key (
        let solver_ctx = State.get solver_ctx_key st in
        { solver_ctx with ctx = cnf }
      ) st
  in

  let handle_get_objectives (_args : DStd.Expr.Term.t list) st =
    let module Sat = (val DO.SatSolverModule.get st) in
    let () =
      if Options.get_interpretation () then
        if not Sat.supports_optimization then
          recoverable_error
            "the selected solver does not support optimization"
        else
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
    st
  in

  let handle_custom_statement loc id args st =
    let args = List.map Dolmen_type.Core.Smtlib2.sexpr_as_term args in
    let logic_file = State.get State.logic_file st in
    let st, terms = Typer.terms st ~input:(`Logic logic_file) ~loc args in
    match id, terms.ret with
    | Dolmen.Std.Id.{name = Simple "minimize"; _}, [term] ->
      cmd_on_modes st [Assert] "minimize";
      handle_optimize_stmt ~is_max:false loc id term st
    | Dolmen.Std.Id.{name = Simple "maximize"; _}, [term] ->
      cmd_on_modes st [Assert] "maximize";
      handle_optimize_stmt ~is_max:true loc id term st
    | Dolmen.Std.Id.{name = Simple "get-objectives"; _}, terms ->
      cmd_on_modes st [Sat] "get-objectives";
      handle_get_objectives terms st
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

  let handle_stmt :
    Frontend.used_context -> State.t ->
    'a D_loop.Typer_Pipe.stmt -> State.t =
    let goal_cnt = ref 0 in
    fun all_context st td ->
      let file_loc = (State.get State.logic_file st).loc in
      let solver_ctx = State.get solver_ctx_key st in
      match td with
      | { contents = `Set_logic _; _} ->
        cmd_on_modes st [Start] "set-logic";
        DO.Mode.set Util.Assert st
      (* When the next statement is a goal, the solver is called and provided
         the goal and the current context *)
      | { id; contents = (`Solve _ as contents); loc ; attrs; implicit } ->
        cmd_on_modes st [Assert; Sat; Unsat] "solve";
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
        let stmt = { Typer_Pipe.id; contents; loc ; attrs; implicit } in
        let cnf, is_thm =
          match D_cnf.make (State.get State.logic_file st).loc l stmt with
          | { Commands.st_decl = Query (_, _, kind); _ } as cnf :: hyps ->
            let is_thm =
              match kind with Ty.Thm | Sat -> true | _ -> false
            in
            List.rev (cnf :: hyps), is_thm
          | _ -> assert false
        in
        let solve_res =
          solve
            (DO.SatSolverModule.get st)
            all_context
            (cnf, name)
        in
        if is_thm
        then
          State.set solver_ctx_key (
            let solver_ctx = State.get solver_ctx_key st in
            { solver_ctx with global = []; local = [] }
          ) st
          |> set_partial_model_and_mode solve_res
        else
          State.set solver_ctx_key (
            let solver_ctx = State.get solver_ctx_key st in
            { solver_ctx with local = [] }
          ) st
          |> set_partial_model_and_mode solve_res

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
        st
        |> State.set partial_model_key None
        |> State.set solver_ctx_key empty_solver_ctx
        |> DO.Mode.clear
        |> DO.StrictMode.clear
        |> DO.ProduceAssignment.clear
        |> DO.init
        |> State.set named_terms Util.MS.empty

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

      | td ->
        let st =
          match td.contents with
          | `Pop _ | `Push _ -> st |> set_mode Assert
          | _ -> st
        in
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
  let handle_stmts all_context st l =
    let rec aux named_map st = function
      | [] -> State.set named_terms named_map st
      | stmt :: tl ->
        let st = handle_stmt all_context st stmt in
        let named_map = add_if_named ~acc:named_map stmt in
        aux named_map st tl
    in
    aux (State.get named_terms st) st l
  in
  let d_fe src =
    let logic_file, st = mk_state src in
    let () = on_strict_mode (O.get_strict_mode ()) in
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
  match O.get_frontend () with
  | "dolmen" -> d_fe src
  | frontend -> ae_fe (O.get_file ()) frontend

let main () =
  let path = Options.get_file () in
  if String.equal path "" then
    process_source ~print_status:Frontend.print_status `Stdin
  else
    process_source ~print_status:Frontend.print_status @@ (`File path)
