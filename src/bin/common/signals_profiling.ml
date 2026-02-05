(******************************************************************************)
(*                                                                            *)
(*  Alt-Ergo: The SMT Solver For Software Verification                        *)
(*  Copyright (C) --- OCamlPro SAS                                            *)
(*                                                                            *)
(*  This software is governed by the CeCILL  license under French law and     *)
(*  abiding by the rules of distribution of free software.  You can  use,     *)
(*  modify and/ or redistribute the software under the terms of the CeCILL    *)
(*  license as circulated by CEA, CNRS and INRIA at the following URL         *)
(*  "http://www.cecill.info".                                                 *)
(*                                                                            *)
(*  As a counterpart to the access to the source code and  rights to copy,    *)
(*  modify and redistribute granted by the license, users are provided only   *)
(*  with a limited warranty  and the software's author,  the holder of the    *)
(*  economic rights,  and the successive licensors  have only  limited        *)
(*  liability.                                                                *)
(*                                                                            *)
(*  In this respect, the user's attention is drawn to the risks associated    *)
(*  with loading,  using,  modifying and/or developing or reproducing the     *)
(*  software by the user in light of its specific status of free software,    *)
(*  that may mean  that it is complicated to manipulate,  and  that  also     *)
(*  therefore means  that it is reserved for developers  and  experienced     *)
(*  professionals having in-depth computer knowledge. Users are therefore     *)
(*  encouraged to load and test the software's suitability as regards their   *)
(*  requirements in conditions enabling the security of their systems and/or  *)
(*  data to be ensured and,  more generally, to use and operate it in the     *)
(*  same conditions as regards security.                                      *)
(*                                                                            *)
(*  The fact that you are presently reading this means that you have had      *)
(*  knowledge of the CeCILL license and that you accept its terms.            *)
(*                                                                            *)
(*  ------------------------------------------------------------------------  *)
(*                                                                            *)
(*  This is a free release of Alt-Ergo under the terms of CeCILL license.     *)
(*  The latest releases of Alt-Ergo are distributed under the terms of        *)
(*  OCamlPro Non-Commercial Purpose License, version 1.                       *)
(*                                                                            *)
(*  ------------------------------------------------------------------------  *)
(*                                                                            *)
(*  The Alt-Ergo theorem prover                                               *)
(*                                                                            *)
(*  Sylvain Conchon, Evelyne Contejean, Francois Bobot                        *)
(*  Mohamed Iguernelala, Stephane Lescuyer, Alain Mebsout                     *)
(*                                                                            *)
(*  CNRS - INRIA - Universite Paris Sud                                       *)
(*                                                                            *)
(*  ------------------------------------------------------------------------  *)
(*                                                                            *)
(*  More details can be found in the directory licenses/                      *)
(*                                                                            *)
(******************************************************************************)

open AltErgoLib
open Options

let timers = Timers.empty ()

let get_timers () = timers

let init_sigterm_6 () =
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
                   timers (get_fmt_err ());
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
            Profiling.print false (Steps.get_steps ()) timers (get_fmt_err ());
         )
      )

let init_sigalarm () =
  if not (get_model ()) then
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
