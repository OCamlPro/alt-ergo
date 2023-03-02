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

(** Lists utilies

    This modules defines some helper functions on lists
*)

(** {3 Misc functions} *)

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

val compare: cmp:('a -> 'a -> int) -> 'a list -> 'a list -> int
(** [compare ~cmp lst1 lst2] compare the lists [lst1] and [lst2]
    using the comparison function [cmp] for their elements. *)

val equal: eq:('a -> 'a -> bool) -> 'a list -> 'a list -> bool
(** [equal ~eq lst1 lst2] check if the lists [lst1] and [lst2] are equal
    using the equality function [eq] for their elements. *)
