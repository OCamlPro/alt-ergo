
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
