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

val pp_smtlib : int -> int -> t Fmt.t
(** [pp_smtlib eb sb ppf v] prints the concrete FP value [v] of precision
    [(eb, sb)] in the SMT-LIB format. *)

val mk_fp_literal :
  neg:bool -> biased_exp:int -> mantissa:Z.t -> e:int -> s:int -> t
(** [mk_fp_literal ~neg ~biased_exp ~mantissa ~e ~s] creates a floating-point
    literal where [neg] is the sign bit, [biased_exp] is the biased exponent,
    [mantissa] is the significand bits (without the hidden bit), [e] is the
    exponent width, and [s] is the significand width (including the hidden bit).
*)
