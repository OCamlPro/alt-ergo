(******************************************************************************)
(*                                                                            *)
(*     Alt-Ergo: The SMT Solver For Software Verification                     *)
(*     Copyright (C) 2018-2018 --- OCamlPro SAS                               *)
(*                                                                            *)
(*     This file is distributed under the terms of the license indicated      *)
(*     in the file 'License.OCamlPro'. If 'License.OCamlPro' is not           *)
(*     present, please contact us to clarify licensing.                       *)
(*                                                                            *)
(******************************************************************************)

val clear_cache : unit -> unit
(** Empties the internal cache of the module. *)

val make :
  D_loop.DStd.Loc.file ->
  Commands.sat_tdecl list ->
  D_loop.Typer_Pipe.typechecked D_loop.Typer_Pipe.stmt ->
  Commands.sat_tdecl list
(** [make acc stmt] Makes one or more [Commands.sat_tdecl] from the
    type-checked statement [stmt] and appends them to [acc].
*)

val make_list :
  D_loop.DStd.Loc.file ->
  D_loop.Typer_Pipe.typechecked D_loop.Typer_Pipe.stmt list ->
  Commands.sat_tdecl list
(** same as [make] but applied to a list, the results are accumulated in the
    returned list.
*)
