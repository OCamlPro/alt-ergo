(******************************************************************************)
(*                                                                            *)
(*     The Alt-Ergo theorem prover                                            *)
(*     Copyright (C) 2006-2013                                                *)
(*                                                                            *)
(*     Sylvain Conchon                                                        *)
(*     Evelyne Contejean                                                      *)
(*                                                                            *)
(*     Francois Bobot                                                         *)
(*     Mohamed Iguernelala                                                    *)
(*     Stephane Lescuyer                                                      *)
(*     Alain Mebsout                                                          *)
(*                                                                            *)
(*     CNRS - INRIA - Universite Paris Sud                                    *)
(*                                                                            *)
(*     This file is distributed under the terms of the Apache Software        *)
(*     License version 2.0                                                    *)
(*                                                                            *)
(*  ------------------------------------------------------------------------  *)
(*                                                                            *)
(*     Alt-Ergo: The SMT Solver For Software Verification                     *)
(*     Copyright (C) 2013-2017 --- OCamlPro SAS                               *)
(*                                                                            *)
(*     This file is distributed under the terms of the Apache Software        *)
(*     License version 2.0                                                    *)
(*                                                                            *)
(******************************************************************************)

type t =
  | Tint
  | Treal
  | Tbool
  | Tunit
  | Tvar of tvar
  | Tbitv of int
  | Text of t list * Hstring.t
  | Tfarray of t * t
  | Tnext of t
  | Tsum of Hstring.t * Hstring.t list
  | Trecord of trecord

and tvar = { v : int ; mutable value : t option }
and trecord = {
  mutable args : t list;
  name : Hstring.t;
  mutable lbs :  (Hstring.t * t) list
}


module M : Map.S with type key = int

type subst = t M.t

val esubst : subst

exception TypeClash of t*t

val tunit : t

val text : t list -> string -> t
val tsum : string -> string list -> t
val trecord : t list -> string -> (string * t) list -> t

val shorten : t -> t

val fresh_var : unit -> tvar
val fresh_tvar : unit -> t

val fresh_empty_text : unit -> t

val fresh : t -> subst -> t * subst
val fresh_list : t list -> subst -> t list * subst

val equal : t -> t -> bool
val hash : t -> int
val compare : t -> t -> int

val unify : t -> t -> unit
val matching : subst -> t -> t -> subst

val apply_subst : subst -> t -> t
val instantiate : t list -> t list -> t -> t

(* Applique la seconde substitution sur la premiere
   puis fais l'union des map avec prioritée à la première *)
val union_subst : subst -> subst -> subst

val compare_subst : subst -> subst -> int
val equal_subst : subst -> subst -> bool

val print : Format.formatter -> t -> unit
val print_list : Format.formatter -> t list -> unit
val print_full : Format.formatter -> t -> unit
(*val printl : Format.formatter -> t list -> unit*)

module Svty : Set.S with type elt = int
module Set : Set.S with type elt = t
val vty_of : t -> Svty.t

val monomorphize: t -> t

val print_subst: Format.formatter -> subst -> unit
