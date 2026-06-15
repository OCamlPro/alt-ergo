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

module DE = Dolmen.Std.Expr

(** The rounding modes for the Floating Point Arithmetic theory. In the legacy
    frontend, the rounding mode type was `fpa_rounding_mode` and defined 5
    rounding modes (see the [rounding_mode] type below). The SMT2 standard
    defines the exact same rounding modes, but with different identifiers. *)

type rounding_mode =
  | NearestTiesToEven
  | ToZero
  | Up
  | Down
  | NearestTiesToAway

val compare_rounding_mode : rounding_mode -> rounding_mode -> int

val fpa_rounding_mode_type_name : string
(** Equal to ["RoundingMode"], the SMT2 type of rounding modes. *)

val fpa_rounding_mode_ae_type_name : string
(** Equal to ["fpa_rounding_mode"], the Alt-Ergo native rounding mode type. *)

val fpa_rounding_mode_dty : Dolmen.Std.Expr.Ty.t
(** The Dolmen rounding mode type. *)

val d_constrs : DE.term_cst list
(** The Dolmen constructors of [rounding_mode]. *)

val fpa_rounding_mode : Ty.t
(** The rounding mode type. *)

val rounding_mode_of_smt : string -> rounding_mode
(** Transforms the string corresponding to a RoundingMode element into the
    [rounding_mode] equivalent. Raises 'Failure' if the string does not
    correspond to a valid rounding mode. *)

val rounding_mode_of_ae : string -> rounding_mode
(** Same, but for legacy's [rounding_mode] equivalent. *)

val translate_smt_rounding_mode : string -> string option
(** Same, but from AE modes to SMT2 modes. *)

val string_of_rounding_mode : rounding_mode -> string
(** Returns the string representation of the [rounding_mode] (SMT2 standard) *)

val term_cst_of_rounding_mode : rounding_mode -> Dolmen.Std.Expr.term_cst
(** Returns the Dolmen constructor associated with the rounding mode. *)

val integer_log_2 : Numbers.Q.t -> int
(** Integer part of binary logarithm for NON-ZERO POSITIVE number **)

val float_of_rational :
  int -> int -> rounding_mode -> Numbers.Q.t -> Numbers.Q.t * Numbers.Z.t * int
(** [float_of_rational prec exp mode x] float approx of a rational constant. The
    function also returns the mantissa and the exponent. i.e. if
    [res, m, e = float_of_rational prec exp mode x], then [res = m * 2^e] **)

val round_to_integer : rounding_mode -> Numbers.Q.t -> Numbers.Q.t
(** [round_to_integer mode x] rounds the rational [x] to an integer depending on
    the rounding mode [mode] *)

val empty_cache : unit -> unit
(** Empties the module's inner cache *)
