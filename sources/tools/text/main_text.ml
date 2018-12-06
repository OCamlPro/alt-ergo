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
open AltErgoParsers
open Options

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
                 Profiling.print true (SAT.get_steps ()) timers fmt;
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
            Profiling.print false (SAT.get_steps ()) timers fmt;
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

let () =
  let d =
    try
      Options.Time.start ();
      Options.Time.set_timeout ~is_gui:false (Options.timelimit ());
      Options.set_is_gui false;
      init_profiling ();

      (*Options.parse_args ();*)
      let filename = get_file () in
      let preludes = Options.preludes () in
      let pfile = Parsers.parse_problem ~filename ~preludes in
      let d, _ = Typechecker.file pfile in
      let d = Typechecker.split_goals_and_cnf d
          [@ocaml.ppwarning "TODO: implement a more efficient split"]
      in
      d
    with Util.Timeout ->
      FE.print_status (FE.Timeout None) 0L;
      exit 142
  in
  let all_used_context = FE.init_all_used_context () in
  match d with
  | [] -> ()
  | [cnf, gname] ->
    begin
      let used_context = FE.choose_used_context all_used_context gname in
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
    if Options.timelimit_per_goal() then
      FE.print_status FE.Preprocess 0L;
    List.iter
      (fun (cnf, gname) ->
         let used_context = FE.choose_used_context all_used_context gname in
         init_profiling ();
         try
           if Options.timelimit_per_goal() then
             begin
               Options.Time.start ();
               Options.Time.set_timeout ~is_gui:false (Options.timelimit ());
             end;
           SAT.reset_refs ();
           ignore
             (List.fold_left (FE.process_decl FE.print_status used_context)
                (SAT.empty (), true, Explanation.empty) cnf)
         with Util.Timeout ->
           if not (Options.timelimit_per_goal()) then exit 142
      ) d;
    Options.Time.unset_timeout ~is_gui:false;

