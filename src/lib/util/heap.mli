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

(** Heaps.

    This modules define intrusive priority heaps (i.e. priority heaps where the
    index of a given element in the map is stored on the element itself).
*)

(** {2 Ranked types}

    Elements that are put in a heap must implement the {!RankedType} interface.
    This requires providing a (loose) comparison function, and allows to get and
    set an `index` field on the element (to map back the element to its current
    position in the heap).

    Note that this implies that each element can only be in a single heap at a
    time. *)

module type RankedType = sig
  type t
  (** The type of the heap elements. *)

  val index : t -> int
  (** Index of the element in the heap. Returns -1 if the element is not in
      the heap. *)

  val set_index : t -> int -> unit
  (** Update the element's index in the heap. *)

  val compare : t -> t -> int
  (** A total ordering function over the set elements.
      This is a two-argument function [f] such that
      [f e1 e2] is zero if the elements [e1] and [e2] are equal,
      [f e1 e2] is strictly negative if [e1] is smaller than [e2],
      and [f e1 e2] is strictly positive if [e1] is greater than [e2]. *)
end

(** {2 Priority heaps} *)

module MakeRanked(Rank : RankedType) : sig
  type elt = Rank.t
  (** The type of elements of the heap. *)

  type t
  (** The type of heaps. *)

  val create : int -> elt -> t
  (** Create a heap with the given initial size and dummy element. *)

  val in_heap : elt -> bool
  (** Heap membership function. *)

  val decrease : t -> elt -> unit
  (** Decrease activity of the given element. *)

  val increase : t -> elt -> unit
  (** Increase activity of the given element. *)

  val size : t -> int
  (** Returns the current size of the heap. *)

  val is_empty : t -> bool
  (** Is the heap empty ? *)

  val insert : t -> elt -> unit
  (** Insert a new element in the heap. *)

  val grow_to_by_double: t -> int -> unit
  (** Grow the size of the heap by multiplying it by 2
      until it is at least the size specified. *)

  val pop_min : t -> elt
  (** Remove the minimum element from the heap and return it.

      @raise Not_found if the heap is empty. *)

  val filter : t -> (elt -> bool) -> unit
  (** Filter elements in the heap. *)
end

(** {2 Ordered priority heaps} *)

module type OrderedTypeDefault = sig
  type t

  val compare : t -> t -> int

  val default : t
  (** Dummy value used in the heap. *)
end

module MakeOrdered(V : OrderedTypeDefault) : sig
  type elt = V.t
  (** The type of elements of the heap. *)

  type t
  (** The type of heaps. *)

  val create : int -> t
  (** Create a heap with the given initial size. *)

  val is_empty : t -> bool
  (** Is the heap empty ? *)

  val insert : t -> elt -> unit
  (** Insert a new element in the heap. *)

  val pop_min : t -> elt
  (** Remove the minimum element from the heap and return it.

      @raise Not_found if the heap is empty. *)
end
