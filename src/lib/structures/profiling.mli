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
(*     The Alt-Ergo theorem prover                                        *)
(*                                                                        *)
(*     Sylvain Conchon, Evelyne Contejean, Francois Bobot                 *)
(*     Mohamed Iguernelala, Stephane Lescuyer, Alain Mebsout              *)
(*                                                                        *)
(*     CNRS - INRIA - Universite Paris Sud                                *)
(*                                                                        *)
(*     ---------------------------------------------------------------    *)
(*                                                                        *)
(*     More details can be found in the directory licenses/               *)
(*                                                                        *)
(**************************************************************************)

val init : unit -> unit
val decision : int -> string -> unit
val assume : int -> unit
val query : unit -> unit
val instantiation : int -> unit
val instances : 'a list -> unit
val bool_conflict : unit -> unit
val theory_conflict : unit -> unit
(* each boolean is true for Boolean conflict and false for Theory conflict *)
val bcp_conflict : bool -> bool -> unit

(* the boolean is true for Boolean red/elim and false for Theory red/elim *)
val red : bool -> unit
val elim : bool -> unit

(* reset decision and matching levels *)
val reset_dlevel : int -> unit
val reset_ilevel : int -> unit

(* record when the axioms are instantiated. Bool tells whether the
   instance is kept or removed by the selector function. The formula
   is the instance that has been generated *)
val new_instance_of : string -> Expr.t -> Dolmen.Std.Loc.loc -> bool -> unit
val conflicting_instance : string -> Dolmen.Std.Loc.loc -> unit
val register_produced_terms :
  string ->
  Dolmen.Std.Loc.loc ->
  Expr.Set.t -> (* consumed *)
  Expr.Set.t -> (* all terms of the instance *)
  Expr.Set.t -> (* produced *)
  Expr.Set.t -> (* produced that are new *)
  unit

val print : bool -> int -> Format.formatter -> unit
val switch : Format.formatter -> unit

val get_timers : unit -> Timers.t

(** Prints the statistics for the SMT statement (get-info :all-statistics). *)
val print_statistics : Format.formatter -> unit
