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

(* workaround to force inclusion of main_input,
   because dune is stupid, :p *)
include Main_input

(* done here to initialize options,
   before the instantiations of functors *)
let () = Options.parse_cmdline_arguments ()

module SatCont = (val (Sat_solver.get_current ()) : Sat_solver_sig.SatContainer)

module TH =
  (val
    (if Options.no_theory() then (module Theory.Main_Empty : Theory.S)
     else (module Theory.Main_Default : Theory.S)) : Theory.S )

module SAT = SatCont.Make(TH)

module FE = Frontend.Make (SAT)

let timers = Timers.empty ()

let () =
  (* what to do with Ctrl+C ? *)
  Sys.set_signal Sys.sigint(*-6*)
    (Sys.Signal_handle (fun _ ->
         if Options.profiling() then Profiling.switch ()
         else begin
           Format.eprintf "; User wants me to stop.\n";
           Format.printf "unknown@.";
           exit 1
         end
       )
    )

let () =
  (* put the test here because Windows does not handle Sys.Signal_handle
     correctly *)
  if Options.profiling() then
    List.iter
      (fun sign ->
         Sys.set_signal sign
           (Sys.Signal_handle
              (fun _ ->
                 Profiling.print true (Steps.get_steps ()) timers fmt;
                 exit 1
              )
           )
      )[ Sys.sigterm (*-11*); Sys.sigquit (*-9*)]

let () =
  (* put the test here because Windows does not handle Sys.Signal_handle
     correctly *)
  if Options.profiling() then
    Sys.set_signal Sys.sigprof (*-21*)
      (Sys.Signal_handle
         (fun _ ->
            Profiling.print false (Steps.get_steps ()) timers fmt;
         )
      )

let () =
  if not (model ()) then
    try
      Sys.set_signal Sys.sigvtalrm
        (Sys.Signal_handle (fun _ -> Options.exec_timeout ()))
    with Invalid_argument _ -> ()

let init_profiling () =
  if Options.profiling () then begin
    Timers.reset timers;
    assert (Options.timers());
    Timers.set_timer_start (Timers.start timers);
    Timers.set_timer_pause (Timers.pause timers);
    Profiling.init ();
  end

(* Internal state while iterating over input statements *)
type 'a state = {
  env : 'a;
  ctx   : Commands.sat_tdecl list;
  local : Commands.sat_tdecl list;
  global : Commands.sat_tdecl list;
}

let solve all_context (cnf, goal_name) =
  let used_context = FE.choose_used_context all_context ~goal_name in
  init_profiling ();
  try
    if Options.timelimit_per_goal() then
      begin
        Options.Time.start ();
        Options.Time.set_timeout ~is_gui:false (Options.timelimit ());
      end;
    SAT.reset_refs ();
    let _ =
      List.fold_left
        (FE.process_decl FE.print_status used_context)
        (SAT.empty (), true, Explanation.empty) cnf
    in
    if Options.profiling() then
      Profiling.print true (Steps.get_steps ()) timers fmt
  with Util.Timeout ->
    if not (Options.timelimit_per_goal()) then exit 142

let typed_loop all_context state td =
  if type_only () then state else begin
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

let () =
  let (module I : Input.S) = Input.find (Options.frontend ()) in
  let parsed =
    try
      Options.Time.start ();
      if not (Options.timelimit_per_goal()) then
        Options.Time.set_timeout ~is_gui:false (Options.timelimit ());

      Options.set_is_gui false;
      init_profiling ();

      let filename = get_file () in
      let preludes = Options.preludes () in
      I.parse_files ~filename ~preludes
    with Util.Timeout ->
      FE.print_status (FE.Timeout None) 0;
      exit 142
  in
  let all_used_context = FE.init_all_used_context () in
  if Options.timelimit_per_goal() then
    FE.print_status FE.Preprocess 0;
  let typing_loop state p =
    if parse_only () then state else begin
      try
        let l, env = I.type_parsed state.env p in
        List.fold_left (typed_loop all_used_context) { state with env; } l
      with
        Errors.Error (e,l) ->
        Loc.report Format.err_formatter l;
        Format.eprintf "typing error: %a\n@." Errors.report e;
        exit 1
    end
  in
  let state = {
    env = I.empty_env;
    ctx = [];
    local = [];
    global = [];
  } in
  let _ : _ state = Seq.fold_left typing_loop state parsed in
  Options.Time.unset_timeout ~is_gui:false;

(*
  match d with
  | [] -> ()
  | [cnf, goal_name] ->
    begin
      let used_context = FE.choose_used_context all_used_context ~goal_name in
      try
        SAT.reset_refs ();
        ignore
          (List.fold_left (FE.process_decl FE.print_status used_context)
             (SAT.empty (), true, Explanation.empty) cnf);
        Options.Time.unset_timeout ~is_gui:false;
        if Options.profiling() then
          Profiling.print true (SAT.get_steps ()) timers fmt;
      with Util.Timeout -> ()
    end
  | _ ->
*)
