(**************************************************************************)
(*                                                                        *)
(*     Alt-Ergo: The SMT Solver For Software Verification                 *)
(*     Copyright (C) --- OCamlPro SAS                                     *)
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
(*     More details can be found in the directory licenses/               *)
(*                                                                        *)
(**************************************************************************)

val clear_cache : unit -> unit
(** Empties the internal cache of the module. *)

val dty_to_ty : ?update:bool -> ?is_var:bool -> D_loop.DStd.Expr.ty -> Ty.t
(** [dty_to_ty update is_var subst tyv_substs dty]

    Converts a Dolmen type to an Alt-Ergo type.
    - If [update] is [true] then for each type variable of type [DE.Ty.Var.t],
      if it was not encountered before, a new type variable of type [Ty.t] is
      created and added to the cache.
    - If [dty] is a type application, or an arrow type, only its return type
      is converted since those have no counterpart in AE's [Ty] module. The
      function arguments' types or the type paramters ought to be converted
      individually.
*)

val make_form :
  string ->
  D_loop.DStd.Expr.term ->
  Loc.t ->
  decl_kind:Expr.decl_kind ->
  Expr.t

val mk_expr :
  ?loc:Loc.t ->
  ?name_base:string ->
  ?toplevel:bool ->
  decl_kind:Expr.decl_kind ->
  Dolmen.Std.Expr.term ->
  Expr.t

val make :
  D_loop.DStd.Loc.file ->
  Commands.sat_tdecl list ->
  [< D_loop.Typer_Pipe.typechecked
  | `Optimize of Dolmen.Std.Expr.term * bool
  | `Goal  of Dolmen.Std.Expr.term
  | `Check of Dolmen.Std.Expr.term list
         > `Hyp ] D_loop.Typer_Pipe.stmt ->
  Commands.sat_tdecl list
(** [make acc stmt] Makes one or more [Commands.sat_tdecl] from the
    type-checked statement [stmt] and appends them to [acc].
*)

val builtins :
  Dolmen_loop.State.t ->
  D_loop.Typer.lang ->
  Dolmen_loop.Typer.T.builtin_symbols
