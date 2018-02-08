(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2017   --   INRIA - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

(*open Format*)

(** Construction *)

exception InvalidConstantLiteral of int * string

type integer_constant = private
  | IConstDec of string
  | IConstHex of string
  | IConstOct of string
  | IConstBin of string

type real_constant = private
  | RConstDec of string * string * string option (* int / frac / exp *)
  | RConstHex of string * string * string option

type constant =
  | ConstInt  of integer_constant
  | ConstReal of real_constant

val int_const_dec : string -> integer_constant
val int_const_hex : string -> integer_constant
val int_const_oct : string -> integer_constant
val int_const_bin : string -> integer_constant
(** these four functions construct integer constant terms from some
    string [s] of digits in the corresponding base. Exception
    InvalidConstantLiteral(base,s) is raised if [s] contains invalid
    characters for the given base.**)
 
val compute_int : integer_constant -> Why3_bigInt.t

val real_const_dec : string -> string -> string option -> real_constant
val real_const_hex : string -> string -> string option -> real_constant

(** Pretty-printing *)
(*
val print_integer_constant : formatter -> integer_constant -> unit
val print_real_constant : formatter -> real_constant -> unit
val print_constant : formatter -> constant -> unit

(** Pretty-printing with conversion *)

type integer_format =
  (string -> unit, Format.formatter, unit) format

type real_format =
  (string -> string -> string -> unit, Format.formatter, unit) format

type part_real_format =
  (string -> string -> unit, Format.formatter, unit) format

type dec_real_format =
  | PrintDecReal of part_real_format * real_format

type frac_real_format =
  | PrintFracReal of integer_format * part_real_format * part_real_format

type 'a number_support_kind =
  | Why3_number_unsupported
  | Why3_number_default
  | Why3_number_custom of 'a

type integer_support_kind = integer_format number_support_kind

type number_support = {
  long_int_support  : bool;
  extra_leading_zeros_support : bool;
  dec_int_support   : integer_support_kind;
  hex_int_support   : integer_support_kind;
  oct_int_support   : integer_support_kind;
  bin_int_support   : integer_support_kind;
  def_int_support   : integer_support_kind;
  dec_real_support  : dec_real_format number_support_kind;
  hex_real_support  : real_format number_support_kind;
  frac_real_support : frac_real_format number_support_kind;
  def_real_support  : integer_support_kind;
}

val print : number_support -> formatter -> constant -> unit

val print_in_base : int -> int option -> formatter -> Why3_bigInt.t -> unit
(** [print_in_base radix digits fmt i] prints the value of [i] in base
    [radix]. If digits is not [None] adds leading 0s to have [digits]
    characters. *)

(** Range checking *)

type int_range = {
  ir_lower : Why3_bigInt.t;
  ir_upper : Why3_bigInt.t;
}

exception OutOfRange of integer_constant

val check_range : integer_constant -> int_range -> unit
(** [check_range c ir] checks that [c] is in the range described
    by [ir], and raises [OutOfRange c] if not. *)

(** Float checking *)

type float_format = {
  fp_exponent_digits    : int;
  fp_significand_digits : int; (* counting the hidden bit *)
}

exception NonRepresentableFloat of real_constant

val compute_float : real_constant -> float_format -> Why3_bigInt.t * Why3_bigInt.t
(** [compute_float c fp] checks that [c] is a float literal
    representable in the format [fp]. Returns a pair [e,s] with
    [s] the significand (without the hidden bit), and [e] the biased
    exponent. Raises [NonRepresentableFloat c] exception otherwise. *)

val check_float : real_constant -> float_format -> unit
(** [check_float c fp] is the same as [compute_float c fp]
    but does not return any value. *)*)
