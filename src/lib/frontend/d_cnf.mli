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

val clear_cache : unit -> unit
(** Empties the internal cache of the module. *)

val make :
  D_loop.DStd.Loc.file ->
  Commands.sat_tdecl list ->
  [< D_loop.Typer_Pipe.typechecked
  | `Goal  of Dolmen.Std.Expr.term
  | `Check of Dolmen.Std.Expr.term list
         > `Hyp ] D_loop.Typer_Pipe.stmt ->
  Commands.sat_tdecl list
(** [make acc stmt] Makes one or more [Commands.sat_tdecl] from the
    type-checked statement [stmt] and appends them to [acc].
*)

val fpa_builtins :
  Dolmen_loop.State.t ->
  D_loop.Typer.lang ->
  Dolmen_loop.Typer.T.builtin_symbols
