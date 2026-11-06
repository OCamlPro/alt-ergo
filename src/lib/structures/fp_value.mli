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
(*     More details can be found in the directory licenses/               *)
(*                                                                        *)
(**************************************************************************)

(** Literal floating-point values. *)

type t =
  | Plus_infinity
  | Minus_infinity
  | Plus_zero
  | Minus_zero
  | NaN
  | Finite of Numbers.Q.t

val compare : t -> t -> int

val equal : t -> t -> bool

val pp : t Fmt.t
(** [pp ppf v] prints the concrete FP value [v] in the Alt-Ergo native format.
*)

val pp_smtlib : eb:int -> sb:int -> t Fmt.t
(** [pp_smtlib ~eb ~sb ppf v] prints the concrete FP value [v] of precision
    [(eb, sb)] in the SMT-LIB format. *)

val mk_fp_literal :
  neg:bool -> biased_exp:int -> mantissa:Z.t -> eb:int -> sb:int -> t
(** [mk_fp_literal ~neg ~biased_exp ~mantissa ~eb ~sb] creates a floating-point
    literal where [neg] is the sign bit, [biased_exp] is the biased exponent,
    [mantissa] is the significand bits (without the hidden bit), [eb] is the
    exponent width, and [sb] is the significand width (including the hidden
    bit). *)

val max_finite_q : eb:int -> sb:int -> Numbers.Q.t
(** [max_finite_q ~eb ~sb] is the largest finite value of the format [(eb, sb)].
*)

val min_normal_q : eb:int -> Numbers.Q.t
(** [min_normal_q ~eb] is the smallest positive normal value of the formats with
    [eb] exponent bits. *)

val is_normal : eb:int -> t -> bool
(** [is_normal ~eb v] holds if [v] is a normal value of a format with [eb]
    exponent bits. *)

val is_subnormal : eb:int -> t -> bool
(** [is_subnormal ~eb v] holds if [v] is a subnormal value of a format with [eb]
    exponent bits. *)

val of_q :
  ?neg_zero:bool ->
  eb:int ->
  sb:int ->
  Fpa_rounding.rounding_mode ->
  Numbers.Q.t ->
  t
(** [of_q ~eb ~sb mode q] rounds [q] to the format [(eb, sb)]. A zero [q] gives
    [-0] if [neg_zero] is true, [+0] otherwise. *)

val to_integer : Fpa_rounding.rounding_mode option -> t -> Numbers.Z.t option
(** [to_integer mode v] rounds the float literal [v] to an integer. [None] if
    [v] is NaN or infinite, or if [mode] is unknown and [v] is not a zero. *)

val convert :
  eb:int -> sb:int -> Fpa_rounding.rounding_mode option -> t -> t option
(** [convert ~eb ~sb mode v] converts the float literal [v] to the format
    [(eb, sb)]. [None] if [mode] is unknown and [v] is finite and nonzero. *)
