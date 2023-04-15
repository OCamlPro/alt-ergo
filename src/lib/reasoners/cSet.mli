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

(* NOTE: If this file is set.mli, do not edit it directly! Instead,
   edit templates/set.template.mli and run tools/sync_stdlib_docs *)

(** Sets over ordered types.

    This module implements the set data structure, given a total ordering
    function over the set elements. All operations over sets
    are purely applicative (no side-effects).
    The implementation uses balanced binary trees, and is therefore
    reasonably efficient: insertion and membership take time
    logarithmic in the size of the set, for instance.

    The {!Make} functor constructs implementations for any type, given a
    [compare] function.
    For instance:
    {[
      module IntPairs =
      struct
        type t = int * int
        let compare (x0,y0) (x1,y1) =
          match Stdlib.compare x0 x1 with
            0 -> Stdlib.compare y0 y1
          | c -> c
      end

      module PairsSet = Set.Make(IntPairs)

      let m = PairsSet.(empty |> add (2,3) |> add (5,7) |> add (11,13))
    ]}

    This creates a new module [PairsSet], with a new type [PairsSet.t]
    of sets of [int * int].
*)

(** {1:sets Sets} *)

type 'a set
(** The type of sets. *)

type 'a setcmp = 'a -> 'a -> int

val empty: 'a set
(** The empty set. *)

val add: 'a setcmp -> 'a -> 'a set -> 'a set
(** [add x s] returns a set containing all elements of [s],
    plus [x]. If [x] was already in [s], [s] is returned unchanged
    (the result of the function is then physically equal to [s]).
    @before 4.03 Physical equality was not ensured. *)

val singleton: 'a -> 'a set
(** [singleton x] returns the one-element set containing only [x]. *)

val remove: 'a setcmp -> 'a -> 'a set -> 'a set
(** [remove x s] returns a set containing all elements of [s],
    except [x]. If [x] was not in [s], [s] is returned unchanged
    (the result of the function is then physically equal to [s]).
    @before 4.03 Physical equality was not ensured. *)

val union: 'a setcmp -> 'a set -> 'a set -> 'a set
(** Set union. *)

val inter: 'a setcmp -> 'a set -> 'a set -> 'a set
(** Set intersection. *)

val disjoint: 'a setcmp -> 'a set -> 'a set -> bool
(** Test if two sets are disjoint.
    @since 4.08 *)

val diff: 'a setcmp -> 'a set -> 'a set -> 'a set
(** Set difference: [diff s1 s2] contains the elements of [s1]
    that are not in [s2]. *)

val cardinal: 'a set -> int
(** Return the number of elements of a set. *)

(** {1:elements Elements} *)

val elements: 'a set -> 'a list
(** Return the list of all elements of the given set.
    The returned list is sorted in increasing order with respect
    to the ordering [Ord.compare], where [Ord] is the argument
    given to {!Set.Make}. *)

val min_elt: 'a set -> 'a
(** Return the smallest element of the given set
    (with respect to the [Ord.compare] ordering), or raise
    [Not_found] if the set is empty. *)

val min_elt_opt: 'a set -> 'a option
(** Return the smallest element of the given set
    (with respect to the [Ord.compare] ordering), or [None]
    if the set is empty.
    @since 4.05 *)

val max_elt: 'a set -> 'a
(** Same as {!min_elt}, but returns the largest element of the
    given set. *)

val max_elt_opt: 'a set -> 'a option
(** Same as {!min_elt_opt}, but returns the largest element of the
    given set.
    @since 4.05 *)

val choose: 'a set -> 'a
(** Return one element of the given set, or raise [Not_found] if
    the set is empty. Which element is chosen is unspecified,
    but equal elements will be chosen for equal sets. *)

val choose_opt: 'a set -> 'a option
(** Return one element of the given set, or [None] if
    the set is empty. Which element is chosen is unspecified,
    but equal elements will be chosen for equal sets.
    @since 4.05 *)

(** {1:searching Searching} *)

val find: 'a setcmp -> 'a -> 'a set -> 'a
(** [find x s] returns the element of [s] equal to [x] (according
    to [Ord.compare]), or raise [Not_found] if no such element
    exists.
    @since 4.01 *)

val find_opt: 'a setcmp -> 'a -> 'a set -> 'a option
(** [find_opt x s] returns the element of [s] equal to [x] (according
    to [Ord.compare]), or [None] if no such element
    exists.
    @since 4.05 *)

val find_first: ('a -> bool) -> 'a set -> 'a
(** [find_first f s], where [f] is a monotonically increasing function,
    returns the lowest element [e] of [s] such that [f e],
    or raises [Not_found] if no such element exists.

    For example, [find_first (fun e -> Ord.compare e x >= 0) s] will
    return the first element [e] of [s] where [Ord.compare e x >= 0]
    (intuitively: [e >= x]), or raise [Not_found] if [x] is greater than
    any element of [s].

    @since 4.05 *)

val find_first_opt: ('a -> bool) -> 'a set -> 'a option
(** [find_first_opt f s], where [f] is a monotonically increasing
    function, returns an option containing the lowest element [e] of [s]
    such that [f e], or [None] if no such element exists.
    @since 4.05
*)

val find_last: ('a -> bool) -> 'a set -> 'a
(** [find_last f s], where [f] is a monotonically decreasing function,
    returns the highest element [e] of [s] such that [f e],
    or raises [Not_found] if no such element exists.
    @since 4.05 *)

val find_last_opt: ('a -> bool) -> 'a set -> 'a option
(** [find_last_opt f s], where [f] is a monotonically decreasing
    function, returns an option containing the highest element [e] of [s]
    such that [f e], or [None] if no such element exists.
    @since 4.05 *)

(** {1:traversing Traversing} *)

val iter: ('a -> unit) -> 'a set -> unit
(** [iter f s] applies [f] in turn to all elements of [s].
    The elements of [s] are presented to [f] in increasing order
    with respect to the ordering over the type of the elements. *)

val fold: ('a -> 'acc -> 'acc) -> 'a set -> 'acc -> 'acc
(** [fold f s init] computes [(f xN ... (f x2 (f x1 init))...)],
    where [x1 ... xN] are the elements of [s], in increasing order. *)

(** {1:transforming Transforming} *)

val map: 'a setcmp -> ('a -> 'a) -> 'a set -> 'a set
(** [map f s] is the set whose elements are [f a0],[f a1]... [f
    aN], where [a0],[a1]...[aN] are the elements of [s].

    The elements are passed to [f] in increasing order
    with respect to the ordering over the type of the elements.

    If no element of [s] is changed by [f], [s] is returned
    unchanged. (If each output of [f] is physically equal to its
    input, the returned set is physically equal to [s].)
    @since 4.04 *)

val filter: ('a -> bool) -> 'a set -> 'a set
(** [filter f s] returns the set of all elements in [s]
    that satisfy predicate [f]. If [f] satisfies every element in [s],
    [s] is returned unchanged (the result of the function is then
    physically equal to [s]).
    @before 4.03 Physical equality was not ensured.*)

val filter_map: 'a setcmp -> ('a -> 'a option) -> 'a set -> 'a set
(** [filter_map f s] returns the set of all [v] such that
    [f x = Some v] for some element [x] of [s].

    For example,
    {[filter_map (fun n -> if n mod 2 = 0 then Some (n / 2) else None) s]}
    is the set of halves of the even elements of [s].

    If no element of [s] is changed or dropped by [f] (if
    [f x = Some x] for each element [x]), then
    [s] is returned unchanged: the result of the function
    is then physically equal to [s].

    @since 4.11 *)

val partition: ('a -> bool) -> 'a set -> 'a set * 'a set
(** [partition f s] returns a pair of sets [(s1, s2)], where
    [s1] is the set of all the elements of [s] that satisfy the
    predicate [f], and [s2] is the set of all the elements of
    [s] that do not satisfy [f]. *)

val split: 'a setcmp -> 'a -> 'a set -> 'a set * bool * 'a set
(** [split x s] returns a triple [(l, present, r)], where
    [l] is the set of elements of [s] that are
    strictly less than [x];
    [r] is the set of elements of [s] that are
    strictly greater than [x];
    [present] is [false] if [s] contains no element equal to [x],
    or [true] if [s] contains an element equal to [x]. *)

(** {1:predicates Predicates and comparisons} *)

val is_empty: 'a set -> bool
(** Test whether a set is empty or not. *)

val mem: 'a setcmp -> 'a -> 'a set -> bool
(** [mem x s] tests whether [x] belongs to the set [s]. *)

val equal: 'a setcmp -> 'a set -> 'a set -> bool
(** [equal s1 s2] tests whether the sets [s1] and [s2] are
    equal, that is, contain equal elements. *)

val compare: 'a setcmp -> 'a set -> 'a set -> int
(** Total ordering between sets. Can be used as the ordering function
    for doing sets of sets. *)

val subset: 'a setcmp -> 'a set -> 'a set -> bool
(** [subset s1 s2] tests whether the set [s1] is a subset of
    the set [s2]. *)

val for_all: ('a -> bool) -> 'a set -> bool
(** [for_all f s] checks if all elements of the set
    satisfy the predicate [f]. *)

val exists: ('a -> bool) -> 'a set -> bool
(** [exists f s] checks if at least one element of
    the set satisfies the predicate [f]. *)

(** {1:converting Converting} *)

val to_list : 'a set -> 'a list
(** [to_list s] is {!elements}[ s].
    @since 5.1 *)

val of_list: 'a setcmp -> 'a list -> 'a set
(** [of_list l] creates a set from a list of elements.
    This is usually more efficient than folding [add] over the list,
    except perhaps for lists with many duplicated elements.
    @since 4.02 *)

val to_seq_from : 'a setcmp -> 'a -> 'a set -> 'a Seq.t
(** [to_seq_from x s] iterates on a subset of the elements of [s]
    in ascending order, from [x] or above.
    @since 4.07 *)

val to_seq : 'a set -> 'a Seq.t
(** Iterate on the whole set, in ascending order
    @since 4.07 *)

val to_rev_seq : 'a set -> 'a Seq.t
(** Iterate on the whole set, in descending order
    @since 4.12 *)

val add_seq : 'a setcmp -> 'a Seq.t -> 'a set -> 'a set
(** Add the given elements to the set, in order.
    @since 4.07 *)

val of_seq : 'a setcmp -> 'a Seq.t -> 'a set
(** Build a set from the given bindings
    @since 4.07 *)
