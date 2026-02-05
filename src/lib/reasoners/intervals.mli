(******************************************************************************)
(*                                                                            *)
(*  Alt-Ergo: The SMT Solver For Software Verification                        *)
(*  Copyright (C) --- OCamlPro SAS                                            *)
(*                                                                            *)
(*  This software is governed by the CeCILL  license under French law and     *)
(*  abiding by the rules of distribution of free software.  You can  use,     *)
(*  modify and/ or redistribute the software under the terms of the CeCILL    *)
(*  license as circulated by CEA, CNRS and INRIA at the following URL         *)
(*  "http://www.cecill.info".                                                 *)
(*                                                                            *)
(*  As a counterpart to the access to the source code and  rights to copy,    *)
(*  modify and redistribute granted by the license, users are provided only   *)
(*  with a limited warranty  and the software's author,  the holder of the    *)
(*  economic rights,  and the successive licensors  have only  limited        *)
(*  liability.                                                                *)
(*                                                                            *)
(*  In this respect, the user's attention is drawn to the risks associated    *)
(*  with loading,  using,  modifying and/or developing or reproducing the     *)
(*  software by the user in light of its specific status of free software,    *)
(*  that may mean  that it is complicated to manipulate,  and  that  also     *)
(*  therefore means  that it is reserved for developers  and  experienced     *)
(*  professionals having in-depth computer knowledge. Users are therefore     *)
(*  encouraged to load and test the software's suitability as regards their   *)
(*  requirements in conditions enabling the security of their systems and/or  *)
(*  data to be ensured and,  more generally, to use and operate it in the     *)
(*  same conditions as regards security.                                      *)
(*                                                                            *)
(*  The fact that you are presently reading this means that you have had      *)
(*  knowledge of the CeCILL license and that you accept its terms.            *)
(*                                                                            *)
(*  ------------------------------------------------------------------------  *)
(*                                                                            *)
(*  This is a free release of Alt-Ergo under the terms of CeCILL license.     *)
(*  The latest releases of Alt-Ergo are distributed under the terms of        *)
(*  OCamlPro Non-Commercial Purpose License, version 1.                       *)
(*                                                                            *)
(*  ------------------------------------------------------------------------  *)
(*                                                                            *)
(*  The Alt-Ergo theorem prover                                               *)
(*                                                                            *)
(*  Sylvain Conchon, Evelyne Contejean, Francois Bobot                        *)
(*  Mohamed Iguernelala, Stephane Lescuyer, Alain Mebsout                     *)
(*                                                                            *)
(*  CNRS - INRIA - Universite Paris Sud                                       *)
(*                                                                            *)
(*  ------------------------------------------------------------------------  *)
(*                                                                            *)
(*  More details can be found in the directory licenses/                      *)
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

val only_borne_sup : t -> t
(** Keep only the upper bound of the interval,
    setting the lower bound to minus infty. *)

val only_borne_inf : t -> t
(** Keep only the lower bound of the interval,
    setting the upper bound to plus infty. *)

val is_point : t -> (Numbers.Q.t * Explanation.t) option

val intersect : t -> t -> t

val exclude : t -> t -> t

val mult : t -> t -> t

val power : int -> t -> t

val sqrt : t -> t

val root : int -> t -> t

val add : t -> t -> t

val scale : Numbers.Q.t -> t -> t

val affine_scale : const:Numbers.Q.t -> coef:Numbers.Q.t -> t -> t
(** Perform an affine transformation on the given bounds.
    Suposing input bounds (b1, b2), this will return
    (const + coef * b1, const + coef * b2).
    This function is useful to avoid the incorrect roundings that
    can take place when scaling down an integer range. *)

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

val coerce : Ty.t -> t -> t
(** Coerce an interval to the given type. The main use of that function is
    to round a rational interval to an integer interval. This is particularly
    useful to avoid roudning too many times when manipulating intervals that
    at the end represent an integer interval, but whose intermediate state do
    not need to represent integer intervals (e.g. computing the interval for
    an integer polynome from the intervals of the monomes). *)

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

val bounds_of : t -> (bnd * bnd) list

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
