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

type t

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
val new_instance_of : string -> Expr.t -> Loc.t -> bool -> unit
val conflicting_instance : string -> Loc.t -> unit
val register_produced_terms :
  string ->
  Loc.t ->
  Expr.Set.t -> (* consumed *)
  Expr.Set.t -> (* all terms of the instance *)
  Expr.Set.t -> (* produced *)
  Expr.Set.t -> (* produced that are new *)
  unit

val print : bool -> int64 -> Timers.t -> Format.formatter -> unit
val switch : unit -> unit
