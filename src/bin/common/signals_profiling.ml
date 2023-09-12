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

let timers = Timers.empty ()

let get_timers () = timers

let init_sigterm_6 () =
  (* what to do with Ctrl+C ? *)
  Sys.set_signal Sys.sigint(*-6*)
    (Sys.Signal_handle (fun _ ->
         if Options.get_profiling() then
           Profiling.switch (Options.Output.get_fmt_diagnostic ())
         else begin
           Printer.print_wrn "User wants me to stop.";
           Printer.print_std "unknown";
           exit 1
         end
       )
    )

let init_sigterm_11_9 () =
  (* put the test here because Windows does not handle Sys.Signal_handle
     correctly *)
  if Options.get_profiling() then
    List.iter
      (fun sign ->
         Sys.set_signal sign
           (Sys.Signal_handle
              (fun _ ->
                 Profiling.print true (Steps.get_steps ())
                   timers (Options.Output.get_fmt_diagnostic ());
                 exit 1
              )
           )
      )[ Sys.sigterm (*-11*); Sys.sigquit (*-9*)]

let init_sigterm_21 () =
  (* put the test here because Windows does not handle Sys.Signal_handle
     correctly *)
  if Options.get_profiling() then
    Sys.set_signal Sys.sigprof (*-21*)
      (Sys.Signal_handle
         (fun _ ->
            Profiling.print false (Steps.get_steps ()) timers
              (Options.Output.get_fmt_diagnostic ());
         )
      )

let init_sigalarm () =
  try
    Sys.set_signal Sys.sigvtalrm
      (Sys.Signal_handle (fun _ -> Options.exec_timeout ()))
  with Invalid_argument _ -> ()

let init_profiling () =
  if Options.get_profiling () then begin
    Timers.reset timers;
    assert (Options.get_timers());
    Timers.set_timer_start (Timers.start timers);
    Timers.set_timer_pause (Timers.pause timers);
    Profiling.init ();
  end

let init_signals () =
  init_sigterm_6 ();
  init_sigterm_11_9 ();
  init_sigterm_21 ();
  init_sigalarm ()
