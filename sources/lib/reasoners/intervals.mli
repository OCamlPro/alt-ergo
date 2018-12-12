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
(*     Copyright (C) 2013-2018 --- OCamlPro SAS                               *)
(*                                                                            *)
(*     This file is distributed under the terms of the Apache Software        *)
(*     License version 2.0                                                    *)
(*                                                                            *)
(******************************************************************************)

type t

exception NotConsistent of Explanation.t
exception No_finite_bound

val undefined : Ty.t -> t

val is_undefined : t -> bool

val point : Numbers.Q.t -> Ty.t -> Explanation.t -> t

val doesnt_contain_0 : t -> Th_util.answer

val is_positive : t -> Th_util.answer

val is_strict_smaller : t -> t -> bool

val new_borne_sup : Explanation.t -> Numbers.Q.t -> is_le : bool -> t -> t

val new_borne_inf : Explanation.t -> Numbers.Q.t -> is_le : bool -> t -> t

val is_point : t -> (Numbers.Q.t * Explanation.t) option

val intersect : t -> t -> t

val exclude : t -> t -> t

val mult : t -> t -> t

val power : int -> t -> t

val sqrt : t -> t

val root : int -> t -> t

val add : t -> t -> t

val scale : Numbers.Q.t -> t -> t

val sub : t -> t -> t

val merge : t -> t -> t

val abs : t -> t

val pretty_print : Format.formatter -> t -> unit

val print : Format.formatter -> t -> unit

val finite_size : t -> Numbers.Q.t option

val borne_inf : t -> Numbers.Q.t * Explanation.t * bool
(** bool is true when bound is large. Raise: No_finite_bound if no
    finite lower bound *)

val borne_sup : t -> Numbers.Q.t * Explanation.t * bool
(** bool is true when bound is large. Raise: No_finite_bound if no
    finite upper bound*)

val div : t -> t -> t

val mk_closed :
  Numbers.Q.t -> Numbers.Q.t -> bool -> bool ->
  Explanation.t -> Explanation.t -> Ty.t -> t
(**
   takes as argument in this order:
   - a lower bound
   - an upper bound
   - a bool that says if the lower bound it is large (true) or strict
   - a bool that says if the upper bound it is large (true) or strict
   - an explanation of the lower bound
   - an explanation of the upper bound
   - a type Ty.t (Tint or Treal *)

type bnd = (Numbers.Q.t * Numbers.Q.t) option * Explanation.t
(* - None <-> Infinity
   - the first number is the real bound
   - the second number if +1 (resp. -1) for strict lower (resp. upper) bound,
     and 0 for large bounds
*)

val  bounds_of : t -> (bnd * bnd) list

val contains : t -> Numbers.Q.t -> bool

val add_explanation : t -> Explanation.t -> t

val equal : t -> t -> bool


type interval_matching =
  ((Numbers.Q.t * bool) option * (Numbers.Q.t * bool) option * Ty.t)
    Var.Map.t

(** matchs the given lower and upper bounds against the given interval, and
    update the given accumulator with the constraints. Returns None if
    the matching problem is inconsistent
*)
val match_interval:
  Symbols.bound -> Symbols.bound -> t -> interval_matching ->
  interval_matching option
