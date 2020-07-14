(******************************************************************************)
(*                                                                            *)
(*     Alt-Ergo: The SMT Solver For Software Verification                     *)
(*     Copyright (C) 2018-2020 --- OCamlPro SAS                               *)
(*                                                                            *)
(*     This file is distributed under the terms of the license indicated      *)
(*     in the file 'License.OCamlPro'. If 'License.OCamlPro' is not           *)
(*     present, please contact us to clarify licensing.                       *)
(*                                                                            *)
(******************************************************************************)

open AltErgoLib
open Options

let init_sig_int () =
  (* what to do with Ctrl+C ? *)
  Sys.set_signal Sys.sigint(*-6*)
    (Sys.Signal_handle (fun _ ->
         if Options.get_profiling() then Profiling.switch (get_fmt_err ())
         else begin
           Printer.print_wrn "User wants me to stop.";
           Printer.print_std "unknown";
           exit 1
         end
       )
    )

let init_sig_term_quit timers =
  (* put the test here because Windows does not handle Sys.Signal_handle
     correctly *)
  if Options.get_profiling() then
    List.iter
      (fun sign ->
         Sys.set_signal sign
           (Sys.Signal_handle
              (fun _ ->
                 Profiling.print true (Steps.get_steps ()) timers
                   (get_fmt_err ());
                 exit 1
              )
           )
      )[ Sys.sigterm (*-11*); Sys.sigquit (*-9*)]

let init_sig_prof timers =
  (* put the test here because Windows does not handle Sys.Signal_handle
     correctly *)
  if Options.get_profiling() then
    Sys.set_signal Sys.sigprof (*-21*)
      (Sys.Signal_handle
         (fun _ ->
            Profiling.print false (Steps.get_steps ()) timers (get_fmt_err ());
         )
      )

let init_sig_vtalarm () =
  if not (get_model ()) then
    try
      Sys.set_signal Sys.sigvtalrm
        (Sys.Signal_handle (fun _ -> Options.exec_timeout ()))
    with Invalid_argument _ -> ()

let init_sig_alarm () =
  if not (get_model ()) then
    try
      Sys.set_signal Sys.sigalrm
        (Sys.Signal_handle (fun _ -> Options.exec_timeout ()))
    with Invalid_argument _ -> ()