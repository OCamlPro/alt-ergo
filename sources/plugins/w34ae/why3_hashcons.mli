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

(** Hash tables for hash consing

    Hash consing tables are using weak pointers, so that values that are no
    more referenced from anywhere else can be erased by the GC.

    Look in src/core/term.ml for usage examples. *)

(** Values to be hash-consed must implement signature [HashedType] below.
    Type [t] is the type of values to be hash-consed.
    The user must provide an equality and a hash function over type [t],
    as well as a function [tag] to build a new value of type [t] from
    an old one and a unique integer tag. *)

module type HashedType =
  sig
    type t
    val equal : t -> t -> bool
    val hash : t -> int
    val tag : int -> t -> t
  end

module type S =
  sig
    type t

    val hashcons : t -> t
      (** [hashcons n] hash-cons value [n] i.e. returns any existing
          value in the table equal to [n], if any; otherwise, creates
          a new value with function [tag], stores it in the table and
          returns it. *)

    val unique : t -> t
      (** [unique n] registers the new value [n] without hash-consing.
          This should be used in case where the value is guaranteed to
          be unique, i.e. not equal to any other value, old or future.
          Unique values are not visited by [iter]. *)

    val iter : (t -> unit) -> unit
      (** [iter f] iterates [f] over all elements of the table. *)

    val stats : unit -> int * int * int * int * int * int
      (** Return statistics on the table.  The numbers are, in order:
          table length, number of entries, sum of bucket lengths,
          smallest bucket length, median bucket length, biggest
          bucket length. *)
  end

module Make(H : HashedType) : (S with type t = H.t)


(* helpers *)

val combine : int -> int -> int
val combine2 : int -> int -> int -> int
val combine3 : int -> int -> int -> int -> int
val combine_list : ('a -> int) -> int -> 'a list -> int
val combine_option : ('a -> int) -> 'a option -> int
val combine_pair : ('a -> int) -> ('b -> int) -> 'a * 'b -> int
