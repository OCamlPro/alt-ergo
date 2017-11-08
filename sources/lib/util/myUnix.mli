(******************************************************************************)
(*                                                                            *)
(*     Alt-Ergo: The SMT Solver For Software Verification                     *)
(*     Copyright (C) 2013-2017 --- OCamlPro SAS                               *)
(*                                                                            *)
(*     This file is distributed under the terms of the license indicated      *)
(*     in the file 'License.OCamlPro'. If 'License.OCamlPro' is not           *)
(*     present, please contact us to clarify licensing.                       *)
(*                                                                            *)
(******************************************************************************)

(** cur_time, provided by Unix or by Javascript depending on the
    compilation mode: for byte/opt or for javascript **)
val cur_time : unit -> float

val set_timeout : is_gui:bool -> float -> unit
val unset_timeout : is_gui:bool -> unit
