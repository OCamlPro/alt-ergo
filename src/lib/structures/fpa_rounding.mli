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

val is_rounding_mode : Expr.t -> bool

val fpa_rounding_mode : Ty.t

(*  why3/standard rounding modes*)

val _NearestTiesToEven__rounding_mode : Expr.t
(** ne in Gappa: to nearest, tie breaking to even mantissas*)

val _ToZero__rounding_mode : Expr.t
(** zr in Gappa: toward zero *)

val _Up__rounding_mode : Expr.t
(** up in Gappa: toward plus infinity *)

val _Down__rounding_mode : Expr.t
(** dn in Gappa: toward minus infinity *)

val _NearestTiesToAway__rounding_mode : Expr.t
(** na : to nearest, tie breaking away from zero *)

(* additional Gappa rounding modes *)

val _Aw__rounding_mode : Expr.t
(** aw in Gappa: away from zero **)

val _Od__rounding_mode : Expr.t
(** od in Gappa: to odd mantissas *)

val _No__rounding_mode : Expr.t
(** no in Gappa: to nearest, tie breaking to odd mantissas *)

val _Nz__rounding_mode : Expr.t
(** nz in Gappa: to nearest, tie breaking toward zero *)

val _Nd__rounding_mode : Expr.t
(** nd in Gappa: to nearest, tie breaking toward minus infinity *)

val _Nu__rounding_mode : Expr.t
(** nu in Gappa: to nearest, tie breaking toward plus infinity *)



(** Integer part of binary logarithm for NON-ZERO POSITIVE number **)
val integer_log_2 : Numbers.Q.t -> int

(** [float_of_rational prec exp mode x] float approx of a rational
    constant.  The function also returns the mantissa and the
    exponent. i.e. if [res, m, e = float_of_rational prec exp mode x],
    then [res = m * 2^e] **)
val float_of_rational :
  Expr.t -> Expr.t -> Expr.t -> Numbers.Q.t -> Numbers.Q.t * Numbers.Z.t * int

(** [round_to_integer mode x] rounds the rational [x] to an integer
    depending on the rounding mode [mode] *)
val round_to_integer:  Expr.t -> Numbers.Q.t -> Numbers.Q.t
