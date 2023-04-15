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

(* NOTE: If this file is map.mli, do not edit it directly! Instead,
   edit templates/map.template.mli and run tools/sync_stdlib_docs *)

(** Association tables over ordered types.

    This module implements applicative association tables, also known as
    finite maps or dictionaries, given a total ordering function
    over the keys.
    All operations over maps are purely applicative (no side-effects).
    The implementation uses balanced binary trees, and therefore searching
    and insertion take time logarithmic in the size of the map.

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

      module PairsMap = Map.Make(IntPairs)

      let m = PairsMap.(empty |> add (0,1) "hello" |> add (1,0) "world")
    ]}

    This creates a new module [PairsMap], with a new type ['a PairsMap.t]
    of maps from [int * int] to ['a]. In this example, [m] contains [string]
    values so its type is [string PairsMap.t].
*)

(** {1:maps Maps} *)

type ('a,'b) map
(** The type of maps from type ['a] to type ['b]. *)

type 'a compare = 'a -> 'a -> int

val empty: ('a,'b) map
(** The empty map. *)

val add: 'a compare -> 'a -> 'b -> ('a,'b) map -> ('a,'b) map
(** [add key data m] returns a map containing the same bindings as
        [m], plus a binding of [key] to [data]. If [key] was already bound
        in [m] to a value that is physically equal to [data],
        [m] is returned unchanged (the result of the function is
        then physically equal to [m]). Otherwise, the previous binding
        of [key] in [m] disappears.
        @before 4.03 Physical equality was not ensured. *)

val add_to_list: 'a compare -> 'a -> 'b -> ('a, 'b list) map -> ('a, 'b list) map
(** [add_to_list key data m] is [m] with [key] mapped to [l] such
    that [l] is [data :: Map.find key m] if [key] was bound in
    [m] and [[v]] otherwise.
    @since 5.1 *)

val update: 'a compare -> 'a -> ('b option -> 'b option) -> ('a,'b) map -> ('a,'b) map
(** [update key f m] returns a map containing the same bindings as
    [m], except for the binding of [key]. Depending on the value of
    [y] where [y] is [f (find_opt key m)], the binding of [key] is
    added, removed or updated. If [y] is [None], the binding is
    removed if it exists; otherwise, if [y] is [Some z] then [key]
    is associated to [z] in the resulting map.  If [key] was already
    bound in [m] to a value that is physically equal to [z], [m]
    is returned unchanged (the result of the function is then
    physically equal to [m]).
    @since 4.06 *)

val singleton: 'a -> 'b -> ('a,'b) map
(** [singleton x y] returns the one-element map that contains a binding
    [y] for [x].
    @since 3.12 *)

val remove: 'a compare -> 'a -> ('a,'b) map -> ('a,'b) map
(** [remove x m] returns a map containing the same bindings as
    [m], except for [x] which is unbound in the returned map.
    If [x] was not in [m], [m] is returned unchanged
    (the result of the function is then physically equal to [m]).
    @before 4.03 Physical equality was not ensured. *)

val merge: 'a compare ->
  ('a -> 'b option -> 'b option -> 'c option) ->
  ('a,'b) map -> ('a,'b) map -> ('a,'c) map
(** [merge f m1 m2] computes a map whose keys are a subset of the keys of
    [m1] and of [m2]. The presence of each such binding, and the
    corresponding value, is determined with the function [f].
    In terms of the [find_opt] operation, we have
    [find_opt x (merge f m1 m2) = f x (find_opt x m1) (find_opt x m2)]
    for any key [x], provided that [f x None None = None].
    @since 3.12 *)

val union: 'a compare -> ('a -> 'b -> 'b -> 'b option) -> ('a,'b) map -> ('a,'b) map -> ('a,'b) map
(** [union f m1 m2] computes a map whose keys are a subset of the keys
    of [m1] and of [m2].  When the same binding is defined in both
    arguments, the function [f] is used to combine them.
    This is a special case of [merge]: [union f m1 m2] is equivalent
    to [merge f' m1 m2], where
    - [f' _key None None = None]
    - [f' _key (Some v) None = Some v]
    - [f' _key None (Some v) = Some v]
    - [f' key (Some v1) (Some v2) = f key v1 v2]

    @since 4.03 *)

val cardinal: ('a,'b) map -> int
(** Return the number of bindings of a map.
    @since 3.12 *)

(** {1:bindings Bindings} *)

val bindings: ('a,'b) map -> ('a * 'b) list
(** Return the list of all bindings of the given map.
    The returned list is sorted in increasing order of keys with respect
    to the ordering [Ord.compare], where [Ord] is the argument
    given to {!Map.Make}.
    @since 3.12 *)

val min_binding: ('a,'b) map -> ('a * 'b)
(** Return the binding with the smallest key in a given map
    (with respect to the [Ord.compare] ordering), or raise
    [Not_found] if the map is empty.
    @since 3.12 *)

val min_binding_opt: ('a,'b) map -> ('a * 'b) option
(** Return the binding with the smallest key in the given map
    (with respect to the [Ord.compare] ordering), or [None]
    if the map is empty.
    @since 4.05 *)

val max_binding: ('a,'b) map -> ('a * 'b)
(** Same as {!min_binding}, but returns the binding with
    the largest key in the given map.
    @since 3.12 *)

val max_binding_opt: ('a,'b) map -> ('a * 'b) option
(** Same as {!min_binding_opt}, but returns the binding with
    the largest key in the given map.
    @since 4.05 *)

val choose: ('a,'b) map -> ('a * 'b)
(** Return one binding of the given map, or raise [Not_found] if
    the map is empty. Which binding is chosen is unspecified,
    but equal bindings will be chosen for equal maps.
    @since 3.12 *)

val choose_opt: ('a,'b) map -> ('a * 'b) option
(** Return one binding of the given map, or [None] if
    the map is empty. Which binding is chosen is unspecified,
    but equal bindings will be chosen for equal maps.
    @since 4.05 *)

(** {1:searching Searching} *)

val find: 'a compare -> 'a -> ('a,'b) map -> 'b
(** [find x m] returns the current value of [x] in [m],
    or raises [Not_found] if no binding for [x] exists. *)

val find_opt: 'a compare -> 'a -> ('a,'b) map -> 'b option
(** [find_opt x m] returns [Some v] if the current value of [x]
    in [m] is [v], or [None] if no binding for [x] exists.
    @since 4.05 *)

val find_first: ('a -> bool) -> ('a,'b) map -> 'a * 'b
(** [find_first f m], where [f] is a monotonically increasing function,
    returns the binding of [m] with the lowest key [k] such that [f k],
    or raises [Not_found] if no such key exists.

    For example, [find_first (fun k -> Ord.compare k x >= 0) m] will
    return the first binding [k, v] of [m] where [Ord.compare k x >= 0]
    (intuitively: [k >= x]), or raise [Not_found] if [x] is greater than
    any element of [m].

    @since 4.05 *)

val find_first_opt: ('a -> bool) -> ('a,'b) map -> ('a * 'b) option
(** [find_first_opt f m], where [f] is a monotonically increasing
    function, returns an option containing the binding of [m] with the
    lowest key [k] such that [f k], or [None] if no such key exists.
    @since 4.05 *)

val find_last: ('a -> bool) -> ('a,'b) map -> 'a * 'b
(** [find_last f m], where [f] is a monotonically decreasing function,
    returns the binding of [m] with the highest key [k] such that [f k],
    or raises [Not_found] if no such key exists.
    @since 4.05 *)

val find_last_opt: ('a -> bool) -> ('a,'b) map -> ('a * 'b) option
(** [find_last_opt f m], where [f] is a monotonically decreasing
    function, returns an option containing the binding of [m] with
    the highest key [k] such that [f k], or [None] if no such key
    exists.
    @since 4.05 *)

(** {1:traversing Traversing} *)

val iter: ('a -> 'b -> unit) -> ('a,'b) map -> unit
(** [iter f m] applies [f] to all bindings in map [m].
    [f] receives the key as first argument, and the associated value
    as second argument.  The bindings are passed to [f] in increasing
    order with respect to the ordering over the type of the keys. *)

val fold:
  ('a -> 'b -> 'acc -> 'acc) -> ('a,'b) map -> 'acc -> 'acc
(** [fold f m init] computes [(f kN dN ... (f k1 d1 init)...)],
    where [k1 ... kN] are the keys of all bindings in [m]
    (in increasing order), and [d1 ... dN] are the associated data. *)

(** {1:transforming Transforming} *)

val map: ('b -> 'b) -> ('a,'b) map -> ('a,'b) map
(** [map f m] returns a map with same domain as [m], where the
    associated value [a] of all bindings of [m] has been
    replaced by the result of the application of [f] to [a].
    The bindings are passed to [f] in increasing order
    with respect to the ordering over the type of the keys. *)

val mapi: ('a -> 'b -> 'b) -> ('a,'b) map -> ('a,'b) map
(** Same as {!map}, but the function receives as arguments both the
    key and the associated value for each binding of the map. *)

val filter: ('a -> 'b -> bool) -> ('a,'b) map -> ('a,'b) map
(** [filter f m] returns the map with all the bindings in [m]
    that satisfy predicate [p]. If every binding in [m] satisfies [f],
    [m] is returned unchanged (the result of the function is then
    physically equal to [m])
    @since 3.12
    @before 4.03 Physical equality was not ensured. *)

val filter_map: ('a -> 'b -> 'b option) -> ('a,'b) map -> ('a,'b) map
(** [filter_map f m] applies the function [f] to every binding of
    [m], and builds a map from the results. For each binding
    [(k, v)] in the input map:
    - if [f k v] is [None] then [k] is not in the result,
    - if [f k v] is [Some v'] then the binding [(k, v')]
      is in the output map.

    For example, the following function on maps whose values are lists
    {[
      filter_map
        (fun _k li -> match li with [] -> None | _::tl -> Some tl)
        m
    ]}
    drops all bindings of [m] whose value is an empty list, and pops
    the first element of each value that is non-empty.

    @since 4.11 *)

val partition: ('a -> 'b -> bool) -> ('a,'b) map -> ('a,'b) map * ('a,'b) map
(** [partition f m] returns a pair of maps [(m1, m2)], where
    [m1] contains all the bindings of [m] that satisfy the
    predicate [f], and [m2] is the map with all the bindings of
    [m] that do not satisfy [f].
    @since 3.12 *)

val split: 'a compare -> 'a -> ('a,'b) map -> ('a,'b) map * 'b option * ('a,'b) map
(** [split x m] returns a triple [(l, data, r)], where
      [l] is the map with all the bindings of [m] whose key
    is strictly less than [x];
      [r] is the map with all the bindings of [m] whose key
    is strictly greater than [x];
      [data] is [None] if [m] contains no binding for [x],
      or [Some v] if [m] binds [v] to [x].
    @since 3.12 *)

(** {1:predicates Predicates and comparisons} *)

val is_empty: ('a,'b) map -> bool
(** Test whether a map is empty or not. *)

val mem: 'a compare -> 'a -> ('a,'b) map -> bool
(** [mem x m] returns [true] if [m] contains a binding for [x],
    and [false] otherwise. *)

val equal: 'a compare -> ('b -> 'b -> bool) -> ('a,'b) map -> ('a,'b) map -> bool
(** [equal cmp m1 m2] tests whether the maps [m1] and [m2] are
    equal, that is, contain equal keys and associate them with
    equal data.  [cmp] is the equality predicate used to compare
    the data associated with the keys. *)

val compare: 'a compare -> ('b -> 'b -> int) -> ('a,'b) map -> ('a,'b) map -> int
(** Total ordering between maps.  The first argument is a total ordering
    used to compare data associated with equal keys in the two maps. *)

val for_all: ('a -> 'b -> bool) -> ('a,'b) map -> bool
(** [for_all f m] checks if all the bindings of the map
    satisfy the predicate [f].
    @since 3.12 *)

val exists: ('a -> 'b -> bool) -> ('a,'b) map -> bool
(** [exists f m] checks if at least one binding of the map satisfies
    the predicate [f].  @since 3.12 *)

(** {1:converting Converting} *)

val to_list : ('a,'b) map -> ('a * 'b) list
(** [to_list m] is {!bindings}[ m].
    @since 5.1 *)

val of_list : 'a compare -> ('a * 'b) list -> ('a,'b) map
(** [of_list bs] adds the bindings of [bs] to the empty map,
    in list order (if a key is bound twice in [bs] the last one
    takes over).
    @since 5.1 *)

val to_seq : ('a,'b) map -> ('a * 'b) Seq.t
(** Iterate on the whole map, in ascending order of keys
    @since 4.07 *)

val to_rev_seq : ('a,'b) map -> ('a * 'b) Seq.t
(** Iterate on the whole map, in descending order of keys
    @since 4.12 *)

val to_seq_from : 'a compare -> 'a -> ('a,'b) map -> ('a * 'b) Seq.t
(** [to_seq_from k m] iterates on a subset of the bindings of [m],
    in ascending order of keys, from key [k] or above.
    @since 4.07 *)

val add_seq : 'a compare -> ('a * 'b) Seq.t -> ('a,'b) map -> ('a,'b) map
(** Add the given bindings to the map, in order.
        @since 4.07 *)

val of_seq : 'a compare -> ('a * 'b) Seq.t -> ('a,'b) map
(** Build a map from the given bindings
    @since 4.07 *)
