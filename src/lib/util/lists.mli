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
(*     ---------------------------------------------------------------    *)
(*                                                                        *)
(*     The Alt-Ergo theorem prover                                        *)
(*                                                                        *)
(*     Sylvain Conchon, Evelyne Contejean, Francois Bobot                 *)
(*     Mohamed Iguernelala, Stephane Lescuyer, Alain Mebsout              *)
(*                                                                        *)
(*     CNRS - INRIA - Universite Paris Sud                                *)
(*                                                                        *)
(*     Until 2013, some parts of this code were released under            *)
(*     the Apache Software License version 2.0.                           *)
(*                                                                        *)
(*     ---------------------------------------------------------------    *)
(*                                                                        *)
(*     More details can be found in the directory licenses/               *)
(*                                                                        *)
(**************************************************************************)

(** Lists utilies

    This modules defines some helper functions on lists
*)

(** {3 Misc functions} *)

val is_empty : 'a list -> bool
(** Is the list empty? *)

val to_seq : 'a list -> 'a Seq.t
(** Iterate on the list *)

val apply : ('a -> 'a) -> 'a list -> 'a list * bool
(** [apply f [a_1; ...; a_n]] returns a couple [[f a_1; ...; f a_n], same]
    same such that: (1) "same" is true if and only if a_i == a_i for
    each i; and (2) if same is true, then the resulting list is
    physically equal to the argument **)

val apply_right : ('a -> 'a) -> ('b * 'a) list -> ('b * 'a) list * bool
(** similar to function apply, but the elements of the list are
    couples **)

val find_opt : ('a -> bool) -> 'a list -> 'a option
(** Tries and find the first element of the list satisfying the predicate. *)

val compare : ('a -> 'a -> int) -> 'a list -> 'a list -> int
(** [compare cmp l1 l2] compares the lists [l1] and [l2] using the comparison
    function [cmp] on elements. *)

val equal : ('a -> 'a -> bool) -> 'a list -> 'a list -> bool
(** [equal eq l1 l2] holds when the two input lists have the same length and for
    each pair of elements [ai], [bi] at the same position in [l1] and [l2]
    respectively, we have [eq ai bi].

    This is a backport of List.equal from OCaml 4.12.0 *)

val partition_map :
  ?keep_ordering:bool ->
  ('a -> ('b, 'c) result) -> 'a list -> 'b list * 'c list
(** Similar to List.partition, but also applies a map on the elements
    of the resulting lists on the fly. Ordering of elements will not be
    kept if [keep_ordering] is unset (Default value is [keep_ordering =
    true]), in which case, resulting lists are reverted *)
