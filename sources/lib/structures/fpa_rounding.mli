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

val is_rounding_mode : Term.t -> bool

val fpa_rounding_mode : Ty.t

(*  why3/standard rounding modes*)

val _NearestTiesToEven__rounding_mode : Term.t
(** ne in Gappa: to nearest, tie breaking to even mantissas*)

val _ToZero__rounding_mode : Term.t
(** zr in Gappa: toward zero *)

val _Up__rounding_mode : Term.t
(** up in Gappa: toward plus infinity *)

val _Down__rounding_mode : Term.t
(** dn in Gappa: toward minus infinity *)

val _NearestTiesToAway__rounding_mode : Term.t
(** na : to nearest, tie breaking away from zero *)

(* additional Gappa rounding modes *)

val _Aw__rounding_mode : Term.t
(** aw in Gappa: away from zero **)

val _Od__rounding_mode : Term.t
(** od in Gappa: to odd mantissas *)

val _No__rounding_mode : Term.t
(** no in Gappa: to nearest, tie breaking to odd mantissas *)

val _Nz__rounding_mode : Term.t
(** nz in Gappa: to nearest, tie breaking toward zero *)

val _Nd__rounding_mode : Term.t
(** nd in Gappa: to nearest, tie breaking toward minus infinity *)

val _Nu__rounding_mode : Term.t
(** nu in Gappa: to nearest, tie breaking toward plus infinity *)



(** Integer part of binary logarithm for NON-ZERO POSITIVE number **)
val integer_log_2 : Numbers.Q.t -> int

(** [float_of_rational prec exp mode x] float approx of a rational
    constant.  The function also returns the mantissa and the
    exponent. i.e. if [res, m, e = float_of_rational prec exp mode x],
    then [res = m * 2^e] **)
val float_of_rational :
  Term.t -> Term.t -> Term.t -> Numbers.Q.t -> Numbers.Q.t * Numbers.Z.t * int

(** [round_to_integer mode x] rounds the rational [x] to an integer
    depending on the rounding mode [mode] *)
val round_to_integer:  Term.t -> Numbers.Q.t -> Numbers.Q.t
