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
(*     More details can be found in the directory licenses/               *)
(*                                                                        *)
(**************************************************************************)

(** Bit-lists provide a domain on bit-vectors that represent the known bits
    sets to [1] and [0], respectively.

    This module provides an implementation of bitlists and related operators.*)

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

val unknown : int -> Explanation.t -> t
(** [unknown w ex] returns an bitlist of width [w] with no known bits. *)

val empty : t
(** An empty bitlist of width 0 and no explanation. *)

val width : t -> int
(** Returns the width of the bitlist. *)

val explanation : t -> Explanation.t
(** Returns the explanation associated with the bitlist. See the type-level
    documentation for details. *)

val exact : int -> Z.t -> Explanation.t -> t
(** [exact w v ex] returns a bitlist of width [w] that represents the [w]-bits
    constant [v]. *)

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

val bits_known : t -> Z.t
(** [bits_known b] returns the sets of bits known to be either [1] or [0] as a
    bitmask. *)

val num_unknown : t -> int
(** [num_unknown b] returns the number of bits unknown in [b]. *)

val is_fully_known : t -> bool
(** [is_fully_known b] determines if there are unknown bits in [b] or not.
    [is_fully_known b] is [true] iff [num_unknown b] is [0]. *)

val value : t -> Z.t
(** [value b] returns the value associated with the bitlist [b]. If the bitlist
    [b] is not fully known, then only the known bits (those that are set in
    [bits_known b]) are meaningful; unknown bits are set to [0]. *)

val intersect : ex:Explanation.t -> t -> t -> t
(** [intersect ~ex b1 b2] returns a new bitlist [b] that subsumes both [b1] and
    [b2]. The explanation [ex] justifies that the two bitlists can be merged.

    Raises [Inconsistent] if [b1] and [b2] are not compatible (i.e. there are
    bits set in one bitlist and cleared in the other). The justification
    includes the justifications of [b1] and [b2], as well as the justification
    [ex] for the intersection. *)

val lognot : t -> t
(** [lognot b] swaps the bits that are set and cleared. *)

val logand : t -> t -> t
(** Bitwise and. *)

val logor : t -> t -> t
(** Bitwise or. *)

val logxor : t -> t -> t
(** Bitwise xor. *)

val concat : t -> t -> t
(** Bit-vector concatenation. *)

val ( @ ) : t -> t -> t
(** Alias for [concat]. *)

val extract : t -> int -> int -> t
(** [extract b i j] returns the bitlist from index [i] to index [j] inclusive.

    The resulting bitlist has length [j - i + 1]. *)
