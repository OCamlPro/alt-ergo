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

(** Lists utilies
    This modules defines some helper functions on lists
*)

(** {3 Misc functions} *)

val assoc : ('a -> 'a -> bool) -> 'a -> ('a * 'b) list -> 'b
(** Similar to [List.assoc] but use a monomorphic comparison function. *)

val assoc_opt : ('a -> 'a -> bool) -> 'a -> ('a * 'b) list -> 'b option
(** Similar to [List.assoc_opt] but use a monomorphic comparison function. *)

val mem_assoc : ('a -> 'a -> bool) -> 'a -> ('a * 'b) list -> bool
(** Similar to [List.mem_assoc] but use a monomorphic comparison function. *)

val remove_assoc : ('a -> 'a -> bool) -> 'a -> ('a * 'b) list -> ('a * 'b) list
(** Similar to [List.remove_assoc] but use a monomorphic comparison function. *)

val apply : ('a -> 'a) -> 'a list -> 'a list * bool
(** [apply f [a_1; ...; a_n]] returns a couple [[f a_1; ...; f a_n], same]
    same such that: (1) "same" is true if and only if a_i == a_i for
    each i; and (2) if same is true, then the resulting list is
    physically equal to the argument *)

val apply_right : ('a -> 'a) -> ('b * 'a) list -> ('b * 'a) list * bool
(** similar to function apply, but the elements of the list are
    couples *)

val try_map : ('a -> 'b option) -> 'a list -> 'b list option
(** [try_map f l] is similar to [List.map f l] but the function [f]
    may fail and the iterator shortcuts the computation. *)

val is_sorted : ('a -> 'a -> int) -> 'a list -> bool
(** [is_sorted cmp l] checks that [l] is sorted for the comparison function
    [cmp]. *)

val iter_pair : (('a * 'b) -> unit) -> ('a list * 'b list) -> unit
(** [iter_pair f (l1, l2)] iterates simultany on the pair of elements of the
    lists [l1] and [l2].

    @raise Invalid_arg if the lists don't have the same length. *)
