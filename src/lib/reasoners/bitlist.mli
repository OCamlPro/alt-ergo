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

(** Bit-lists provide a domain on bit-vectors that represent the known bits
    sets to [1] and [0], respectively.

    This module provides an implementation of bitlists and related operators.
    The bitlists provided by this module do not have a fixed width, and can
    represent arbitrary-precision integers. *)

type t
(** The type of bitlists.

    Bitlists are indexed from the right: the least-significant bit has index
    [0].

    Bitlists include an explanation (that can be recovered through the
    [explanation] function). The explanation indicates why the bitlist applies
    to a value, which must be maintained separately.

    The explanation associated with the result of any bitlist operation is the
    union of the explanations associated with its arguments. *)

val pp : t Fmt.t
(** Pretty-printer for bitlists *)

exception Inconsistent of Explanation.t
(** Exception raised when an inconsistency is detected. *)

val unknown : t
(** [unknown] is a bitlist that repersents all integers. *)

val explanation : t -> Explanation.t
(** Returns the explanation associated with the bitlist. See the type-level
    documentation for details. *)

val exact : Z.t -> Explanation.t -> t
(** [exact v ex] returns a bitlist that represents the constant [v]. *)

val equal : t -> t -> bool
(** [equal b1 b2] returns [true] if the bitlists [b1] and [b2] are equal, albeit
    with possibly different explanations. *)

val ones : t -> t
(** [ones b] returns a bitlist where the zero bits in [b] are replaced with
    unknown bits. *)

val zeroes : t -> t
(** [zeroes b] returns a bitlist where the one bits in [b] are replaced with
    unknown bits. *)

val add_explanation : ex:Explanation.t -> t -> t
(** [add_explanation ~ex b] adds the explanation [ex] to the bitlist [b]. The
    returned bitlist has both the explanation of [b] and [ex] as explanation. *)

val unknown_bits : t -> Z.t
(** [unknown_bits b] returns the set of unknown (or undetermined) bits in [b].

    The value of [Z.logand (Z.lognot (unknown_bits b)) n] is the same for any
    [n] in the set represented by the bitlist [b]. *)

val is_fully_known : t -> bool
(** [is_fully_known b] determines if there are unknown bits in [b] or not.
    [is_fully_known b] is [true] iff [unknown_bits b] is [Z.zero]. *)

val value : t -> Z.t
(** [value b] returns the value associated with the bitlist [b]. If the bitlist
    [b] is not fully known, then only the known bits (those that are set in
    [bits_known b]) are meaningful; unknown bits are set to [0]. *)

val intersect : t -> t -> t
(** [intersect b1 b2] returns a new bitlist [b] that subsumes both [b1] and
    [b2]. Any explanation justifying that [b1] and [b2] apply to the same
    value must have been added to [b1] and [b2].

    Raises [Inconsistent] if [b1] and [b2] are not compatible (i.e. there are
    bits set in one bitlist and cleared in the other). *)

val lognot : t -> t
(** [lognot b] swaps the bits that are set and cleared. *)

val logand : t -> t -> t
(** Bit-wise and. *)

val logor : t -> t -> t
(** Bit-wise or. *)

val logxor : t -> t -> t
(** Bit-wise xor. *)

val add : t -> t -> t
(** Addition. *)

val sub : t -> t -> t
(** Subtraction. *)

val mul : t -> t -> t
(** Integer multiplication. *)

val bvshl : size:int -> t -> t -> t
(** Logical left shift, truncated to the [size] least significant bits. *)

val bvlshr : size:int -> t -> t -> t
(** Logical right shift, truncated to the [size] least significant bits. *)

val shift_left : t -> int -> t
(** Shifts to the left. Equivalent to a multiplication by a power of [2]. The
    second argument must be nonnegative. *)

val shift_right : t -> int -> t
(** Shifts to the right. This is an arithmetic shift, equivalent to a division
    by a power of [2] with rounding towards -oo. The second argument must be
    nonnegative. *)

val extract : t -> int -> int -> t
(** [extract b off len] returns a nonnegative bitlist corresponding to bits
    [off] to [off + len - 1] of [b].

    {b Note}: This uses the same arguments as [Z.extract], not the arguments
    from the SMT-LIB's [extract] primitive. *)

val increase_lower_bound : t -> Z.t -> Z.t
(** [increase_lower_bound b lb] returns the smallest integer [lb' >= lb] that
    matches the bit-pattern in [b].

    @raise Not_found if no such integer exists. *)

val decrease_upper_bound : t -> Z.t -> Z.t
(** [decrease_upper_bound b ub] returns the largest integer [ub' >= ub] that
    matches the bit-pattern in [b].

    @raise Not_found if no such integer exists. *)

(** {2 Prefix and infix operators} *)

val ( land ) : t -> t -> t
(** Bit-wise logical and [logand]. *)

val ( lor ) : t -> t -> t
(** Bit-wise logical inclusive or [logor]. *)

val ( lxor ) : t -> t -> t
(** Bit-wise logical exclusive xor [logxor]. *)

val ( ~! ) : t -> t
(** Bit-wise logical negation [lognot]. *)

val ( lsl ) : t -> int -> t
(** Bit-wise shift to the left [shift_left]. *)

val ( asr ) : t -> int -> t
(** Bit-wise shift to the right [shift_right]. *)

(**/**)

(** [fold_finite_domain f i acc] accumulates [f] on all the elements of [i] (in
    an unspecified order). Intended for testing purposes only.

    @raise Invalid_argument if the bitlist is [empty]. *)
val fold_domain : (Z.t -> 'a -> 'a) -> t -> 'a -> 'a
