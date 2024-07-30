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

type 'a t = {
  mutable data : 'a array;
  mutable sz : int;
  dummy: 'a;
}
(** Type of vectors of 'a elements. *)

val make : int -> dummy:'a -> 'a t
(** [make cap dummy] creates a new vector filled with [dummy]. The vector
    is initially empty but its underlying array has capacity [cap].
    [dummy] will stay alive as long as the vector *)

val create : dummy:'a -> 'a t
(** [create ~dummy] creates an empty vector using [dummy] as dummy values. *)

val to_list : 'a t -> 'a list
(** Returns the list of elements of the vector. *)

val to_rev_list : 'a t -> 'a list
(** Returns the list of elements of the vector in reversed order. *)

val to_array : 'a t -> 'a array

val of_list : 'a list -> dummy:'a -> 'a t

val clear : 'a t -> unit
(** [clear vec] sets the size of [vec] to zero and free the elements. *)

val shrink : 'a t -> int -> unit
(** [shrink vec sz] resets size of [vec] to [sz] and frees its elements.
    Assumes [sz >=0 && sz <= size vec]. *)

val pop : 'a t -> 'a
(** Pop last element, free and return it.
    @raise Invalid_argument if the vector is empty. *)

val last : 'a t -> 'a
(** Return the last element.
    @raise Invalid_argument if the vector is empty. *)

val grow_to_by_double : 'a t -> int -> unit
(** [grow_to_by_double vec c] grow the capacity of the vector
    by double it. *)

val size : 'a t -> int
(** Returns the size of the vector. *)

val is_empty : 'a t -> bool
(** Returns [true] if and only if the vector is of size 0. *)

val is_full : 'a t -> bool
(** Is the capacity of the vector equal to the number of its elements? *)

val push : 'a t -> 'a -> unit
(** Push element into the vector. *)

val get : 'a t -> int -> 'a
(** Get the element at the given index, or
    @raise Assert_failure if the index is not valid. *)

val set : 'a t -> int -> 'a -> unit
(** Set the element at the given index, either already set or the first
    free slot if [not (is_full vec)], or
    @raise Invalid_argument if the index is not valid. *)

val replace : (' a -> 'a) -> 'a t -> int -> unit
(** [replace f vec n] is equalivalent to [set vec n (f (get vec n))],
    but with a single bound check.

    @raise Assert_failure if the index is not valid. *)

val copy : 'a t -> 'a t
(** Fresh copy. *)

val fast_remove : 'a t -> int -> unit
(** Remove element at index [i] without preserving order
    (swap with last element). *)

val filter_in_place : ('a -> bool) -> 'a t -> unit
(** [filter_in_place p vec] removes from [vec] the elements that do
    not satisfy [p]. *)

val sort : 'a t -> ('a -> 'a -> int) -> unit
(** Sort in place the vector. *)

val iter : ('a -> unit) -> 'a t -> unit
(** Iterate on elements. *)

val iteri : (int -> 'a -> unit) -> 'a t -> unit
(** Iterate on elements with their index. *)

val fold : ('b -> 'a -> 'b) -> 'b -> 'a t -> 'b
(** Fold over elements. *)

val exists : ('a -> bool) -> 'a t -> bool
(** Does there exist an element that satisfies the predicate? *)

val for_all : ('a -> bool) -> 'a t -> bool
(** Do all elements satisfy the predicate? *)

val pp : 'a Fmt.t -> 'a t Fmt.t
(** [pp pp_elt ppf vec] prints on the formatter [ppf] all the elements of [vec]
    using the printer [pp_elt]. Dummy values are also printed. *)
