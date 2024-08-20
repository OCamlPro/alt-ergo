(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*             Xavier Leroy, projet Cristal, INRIA Rocquencourt           *)
(*                                                                        *)
(*   Copyright 1996 Institut National de Recherche en Informatique et     *)
(*     en Automatique.                                                    *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

module List : sig
  val is_empty : 'a list -> bool
  (** [is_empty l] is true if and only if [l] has no elements. It is equivalent
      to [compare_length_with l 0 = 0].

      @since OCaml 5.1 *)

  val equal : ('a -> 'a -> bool) -> 'a list -> 'a list -> bool
  (** [equal eq [a1; ...; an] [b1; ..; bm]] holds when
      the two input lists have the same length, and for each
      pair of elements [ai], [bi] at the same position we have
      [eq ai bi].

      Note: the [eq] function may be called even if the
      lists have different length. If you know your equality
      function is costly, you may want to check {!compare_lengths}
      first.

      @since OCaml 4.12 *)

  val compare : ('a -> 'a -> int) -> 'a list -> 'a list -> int
  (** [compare cmp [a1; ...; an] [b1; ...; bm]] performs
      a lexicographic comparison of the two input lists,
      using the same ['a -> 'a -> int] interface as {!Stdlib.compare}:

      - [a1 :: l1] is smaller than [a2 :: l2] (negative result)
        if [a1] is smaller than [a2], or if they are equal (0 result)
        and [l1] is smaller than [l2]
      - the empty list [[]] is strictly smaller than non-empty lists

      Note: the [cmp] function will be called even if the lists have
      different lengths.

      @since OCaml 4.12 *)

  val find_map : ('a -> 'b option) -> 'a list -> 'b option
  (** [find_map f l] applies [f] to the elements of [l] in order,
      and returns the first result of the form [Some v], or [None]
      if none exist.

      @since OCaml 4.10 *)

  val fold_left_map :
    ('acc -> 'a -> 'acc * 'b) -> 'acc -> 'a list -> 'acc * 'b list
    (** [fold_left_map] is  a combination of [fold_left] and [map] that
        threads an accumulator through calls to [f].

        @since OCaml 4.11 *)
end

module String : sig
  val fold_left : ('acc -> char -> 'acc) -> 'acc -> string -> 'acc
  (** [fold_left f x s] computes [f (... (f (f x s.[0]) s.[1]) ...) s.[n-1]],
      where [n] is the length of the string [s].

      @since OCaml 4.13 *)

  val starts_with : prefix :string -> string -> bool
  (** [starts_with ~prefix s] is [true] if and only if [s] starts with
      [prefix].

      @since OCaml 4.13 *)
end

module Seq : sig
  val uncons : 'a Seq.t -> ('a * 'a Seq.t) option
  (** If [xs] is empty, then [uncons xs] is [None].

      If [xs] is nonempty, then [uncons xs] is [Some (x, ys)] where [x] is the
      head of the sequence and [ys] its tail.

      @since OCaml 4.14 *)

  val is_empty : 'a Seq.t -> bool
  (** [is_empty xs] determines whether the sequence [xs] is empty.

      It is recommended that the sequence [xs] be persistent.
      Indeed, [is_empty xs] demands the head of the sequence [xs],
      so, if [xs] is ephemeral, it may be the case that [xs] cannot
      be used any more after this call has taken place.

      @since OCaml 4.14 *)

  val append : 'a Seq.t -> 'a Seq.t -> 'a Seq.t
  (** [append xs ys] is the concatenation of the sequences [xs] and [ys].

      Its elements are the elements of [xs], followed by the elements of [ys].

      @since OCaml 4.11 *)

  val equal : ('a -> 'b -> bool) -> 'a Seq.t -> 'b Seq.t -> bool
  (** Provided the function [eq] defines an equality on elements,
      [equal eq xs ys] determines whether the sequences [xs] and [ys]
      are pointwise equal.

      At least one of the sequences [xs] and [ys] must be finite.

      @since OCaml 4.14 *)
end

module Type : sig
  (** Type introspection.

      @since OCaml 5.1 *)

  type (_, _) eq = Equal: ('a, 'a) eq (** *)
  (** The purpose of [eq] is to represent type equalities that may not
      otherwise
      be known by the type checker (e.g. because they may depend on dynamic
      data).

      A value of type [(a, b) eq] represents the fact that types [a] and [b]
      are equal.

      If one has a value [eq : (a, b) eq] that proves types [a] and [b] are
      equal, one can use it to convert a value of type [a] to a value of
      type [b] by pattern matching on [Equal]:
      {[
        let cast (type a) (type b) (Equal : (a, b) Type.eq) (a : a) : b = a
      ]}

      At runtime, this function simply returns its second argument
      unchanged.
  *)

  (** {1:identifiers Type identifiers} *)

  (** Type identifiers.

      A type identifier is a value that denotes a type. Given two type
      identifiers, they can be tested for {{!Id.provably_equal}equality} to
      prove they denote the same type. Note that:

      - Unequal identifiers do not imply unequal types: a given type can be
        denoted by more than one identifier.
      - Type identifiers can be marshalled, but they get a new, distinct,
        identity on unmarshalling, so the equalities are lost. *)
  module Id : sig

    (** {1:ids Type identifiers} *)

    type 'a t
    (** The type for identifiers for type ['a]. *)

    val make : unit -> 'a t
    (** [make ()] is a new type identifier. *)

    val uid : 'a t -> int
    (** [uid id] is a runtime unique identifier for [id]. *)

    val provably_equal : 'a t -> 'b t -> ('a, 'b) eq option
    (** [provably_equal i0 i1] is [Some Equal] if identifier [i0] is equal
        to [i1] and [None] otherwise. *)
  end
end
