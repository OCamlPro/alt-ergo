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
(*     Copyright (C) 2013-2017 --- OCamlPro SAS                               *)
(*                                                                            *)
(*     This file is distributed under the terms of the Apache Software        *)
(*     License version 2.0                                                    *)
(*                                                                            *)
(******************************************************************************)

open Typed
open Lexing
open Format
open Options

module SAT = (val (Sat_solver.get_current ()) : Sat_solver_sig.S)
module FE = Frontend.Make (SAT)

let timers = Timers.empty ()

let () =
  (* what to do with Ctrl+C ? *)
  Sys.set_signal Sys.sigint(*-6*)
    (Sys.Signal_handle (fun _ ->
      if Options.profiling() then Profiling.switch ()
      else (print_endline "User wants me to stop."; exit 1)
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

let () =
  try
    Options.set_is_gui false;
    Options.Time.start ();
    Options.Time.set_timeout ~is_gui:false (Options.timelimit ());
    if Options.profiling () then begin
      Timers.reset timers;
      assert (Options.timers());
      Timers.set_timer_start (Timers.start timers);
      Timers.set_timer_pause (Timers.pause timers);
      Profiling.init ();
    end;

  (*Options.parse_args ();*)
    let filename = get_file () in
    let preludes = Options.preludes () in
    let pfile = Parsers.parse_problem ~filename ~preludes in
    let d = FE.typecheck_file pfile in

    let d =
      List.map
        (fun d ->  Cnf.make (List.map (fun (f, env) -> f, true) d)) d
    in
    List.iter
      (fun cnf ->
        SAT.reset_refs ();
        ignore (Queue.fold (FE.process_decl FE.print_status)
		  (SAT.empty (), true, Explanation.empty) cnf)
      ) d;
    Options.Time.unset_timeout ~is_gui:false;
    if Options.profiling() then
      Profiling.print true (SAT.get_steps ()) timers fmt;
  with Util.Timeout ->
    Format.eprintf "Timeout@.";
    exit 142
