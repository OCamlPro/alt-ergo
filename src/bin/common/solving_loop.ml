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

(* Internal state while iterating over input statements *)
type 'a state = {
  env : 'a;
  ctx   : Commands.sat_tdecl list;
  local : Commands.sat_tdecl list;
  global : Commands.sat_tdecl list;
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
        let l = state.local @ state.global @ state.ctx in
        let cnf = List.rev @@ Cnf.make l td in
        let () = solve all_context (cnf, name) in
        begin match kind with
          | Typed.Check
          | Typed.Cut -> { state with local = []; }
          | _ -> { state with global = []; local = []; }
        end
      | Typed.TAxiom (_, s, _, _) when Typed.is_global_hyp s ->
        let cnf = Cnf.make state.global td in
        { state with global = cnf; }
      | Typed.TAxiom (_, s, _, _) when Typed.is_local_hyp s ->
        let cnf = Cnf.make state.local td in
        { state with local = cnf; }
      | _ ->
        let cnf = Cnf.make state.ctx td in
        { state with ctx = cnf; }
    end
  in

  let (module I : Input.S) = Input.find (Options.get_frontend ()) in

  let parsed () =
    try
      Options.Time.start ();
      if not (Options.get_timelimit_per_goal()) then
        Options.Time.set_timeout ~is_gui:false (Options.get_timelimit ());

      Options.set_is_gui false;
      Signals_profiling.init_profiling ();

      let filename = get_file () in
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
    ctx = [];
    local = [];
    global = [];
  } in
  try
    let _ : _ state = Seq.fold_left typing_loop state (parsed ()) in
    Options.Time.unset_timeout ~is_gui:false;
  with Util.Timeout ->
    FE.print_status (FE.Timeout None) 0;
    exit 142
