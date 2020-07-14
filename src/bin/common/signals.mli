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


(** {1 Signals module used at start-up to handle  signals for system} *)

(** Add signal handler for Ctrl+C,
    if profiling is set, swotch beetwen display
    else print warning message and unknown and then exit 1 *)
val init_sig_int : unit -> unit

(** Add signal handler for termination signal if profiling is set.
    print steps counter and then exit 1 *)
val init_sig_term_quit : AltErgoLib.Timers.t -> unit

(** Add signal handler for profiling interruption signal if profiling is set.
    Print steps counter. *)
val init_sig_prof : AltErgoLib.Timers.t -> unit

(** Add signal handler for alarm signal (timeout). Raise timeout *)
val init_sig_alarm : unit -> unit

(** Add signal handler for virtual alarm signal (timeout). Raise timeout *)
val init_sig_vtalarm : unit -> unit