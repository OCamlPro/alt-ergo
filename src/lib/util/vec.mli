(******************************************************************************)
(*                                                                            *)
(*     Alt-Ergo: The SMT Solver For Software Verification                     *)
(*     Copyright (C) 2013-2018 --- OCamlPro SAS                               *)
(*                                                                            *)
(*     This file is distributed under the terms of the license indicated      *)
(*     in the file 'License.OCamlPro'. If 'License.OCamlPro' is not           *)
(*     present, please contact us to clarify licensing.                       *)
(*                                                                            *)
(******************************************************************************)

type 'a t = {
  mutable data : 'a array;
  mutable sz : int;
  dummy: 'a;
}
(** Type of sparse vectors of 'a elements. *)

val make : int -> dummy:'a -> 'a t
(** [make cap dummy] creates a new vector filled with [dummy]. The vector
    is initially empty but its underlying array has capacity [cap].
    [dummy] will stay alive as long as the vector *)

val create : dummy:'a -> 'a t
(** [create ~dummy] creates an empty vector using [dummy] as dummy values. *)

val to_list : 'a t -> 'a list
(** Returns the list of elements of the vector. *)

val to_array : 'a t -> 'a array

val of_list : 'a list -> dummy:'a -> 'a t

val clear : 'a t -> unit
(** Set size to zero, doesn't free elements. *)

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
(** get the element at the given index, or
    @raise Invalid_argument if the index is not valid. *)

val set : 'a t -> int -> 'a -> unit
(** set the element at the given index, either already set or the first
    free slot if [not (is_full vec)], or
    @raise Invalid_argument if the index is not valid. *)

val copy : 'a t -> 'a t
(** Fresh copy. *)

val fast_remove : 'a t -> int -> unit
(** Remove element at index [i] without preserving order
    (swap with last element). *)

val filter_in_place : ('a -> bool) -> 'a t -> unit
(** [filter_in_place f v] removes from [v] the elements that do
    not satisfy [f] *)

val sort : 'a t -> ('a -> 'a -> int) -> unit
(** Sort in place the vector. *)

val iter : ('a -> unit) -> 'a t -> unit
(** Iterate on elements. Ignore dummy elements. *)

val iteri : (int -> 'a -> unit) -> 'a t -> unit
(** Iterate on elements with their index. Ignore dummy elements. *)

val fold : ('b -> 'a -> 'b) -> 'b -> 'a t -> 'b
(** Fold over elements. Ignore dummy elements. Ignore dummy elements. *)

val exists : ('a -> bool) -> 'a t -> bool
(** Does there exist a non-dummy element that satisfies the predicate? *)

val for_all : ('a -> bool) -> 'a t -> bool
(** Do all non-dummy elements satisfy the predicate? *)

val pp :
  ?sep:string ->
  (Format.formatter -> 'a -> unit) ->
  Format.formatter -> 'a t -> unit
(** [pp ~sep pp_elt fmt vec] prints on the formatter [fmt]
    all the elements of [vec] using the printer [pp_elt] for each element. *)
