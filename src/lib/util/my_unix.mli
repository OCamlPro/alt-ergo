(******************************************************************************)
(*                                                                            *)
(*     Alt-Ergo: The SMT Solver For Software Verification                     *)
(*     Copyright (C) 2013-2018 --- OCamlPro SAS                               *)
(*                                                                            *)
(*     This file is distributed under the terms of the license indicated      *)
(*     in the file 'License.OCamlPro'. If 'License.OCamlPro' is not           *)
(*     present, please contact us to clarify licensing.                       *)
(*                                                                            *)
(******************************************************************************)

(** Unix wrapper

    This module defines some wrappers around Unix function,
    in order to more easily maintain compatibility when
    compiling to javascript.
*)

val cur_time : unit -> float
(** Returns the current time. **)

val set_timeout : is_gui:bool -> float -> unit
(** Set a timeout, using Unix timers.
    If [is_gui] then the timer raises {!Unix.ITIMER_REAL},
    else raises {!Unix.ITIMER_VIRTUAL}.
    No-op on javascript. *)

val unset_timeout : is_gui:bool -> unit
(** Unset the previously set timer. *)

