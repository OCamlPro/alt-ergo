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

type rounding_mode =
  (* five standard/why3 fpa rounding modes *)
  | NearestTiesToEven
  (*ne in Gappa: to nearest, tie breaking to even mantissas*)
  | ToZero (* zr in Gappa: toward zero *)
  | Up (* up in Gappa: toward plus infinity *)
  | Down (* dn in Gappa: toward minus infinity *)
  | NearestTiesToAway (* na : to nearest, tie breaking away from zero *)

  (* additional Gappa rounding modes *)
  | Aw (* aw in Gappa: away from zero **)
  | Od (* od in Gappa: to odd mantissas *)
  | No (* no in Gappa: to nearest, tie breaking to odd mantissas *)
  | Nz (* nz in Gappa: to nearest, tie breaking toward zero *)
  | Nd (* nd in Gappa: to nearest, tie breaking toward minus infinity *)
  | Nu (* nu in Gappa: to nearest, tie breaking toward plus infinity *)

val fpa_rounding_mode : Ty.t

val rounding_mode_of_hs : Hstring.t -> rounding_mode

(** Integer part of binary logarithm for NON-ZERO POSITIVE number **)
val integer_log_2 : Numbers.Q.t -> int

(** [float_of_rational prec exp mode x] float approx of a rational
    constant.  The function also returns the mantissa and the
    exponent. i.e. if [res, m, e = float_of_rational prec exp mode x],
    then [res = m * 2^e] **)
val float_of_rational :
  int -> int -> rounding_mode -> Numbers.Q.t -> Numbers.Q.t * Numbers.Z.t * int

(** [round_to_integer mode x] rounds the rational [x] to an integer
    depending on the rounding mode [mode] *)
val round_to_integer:  rounding_mode -> Numbers.Q.t -> Numbers.Q.t

(** Empties the module's inner cache *)
val empty_cache : unit -> unit
