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

type ty_module =
  | M_None
  | M_Combine
  | M_Typing
  | M_Sat
  | M_Match
  | M_CC
  | M_UF
  | M_Arith
  | M_Arrays
  | M_Adt
  | M_Bitv
  | M_AC
  | M_Expr
  | M_Triggers
  | M_Simplex
  | M_Ite

type ty_function =
  | F_add
  | F_add_lemma
  | F_add_predicate
  | F_add_terms
  | F_are_equal
  | F_assume
  | F_class_of
  | F_leaves
  | F_make
  | F_m_lemmas
  | F_m_predicates
  | F_query
  | F_solve
  | F_subst
  | F_union
  | F_unsat
  | F_none
  | F_new_facts
  | F_apply_subst
  | F_instantiate

(** environment of internal timers **)
type t

(** return a new empty env **)
val empty : unit -> t

(** reset the given env to empty *)
val reset : t -> unit

(** save the current timer and start the timer "ty_module x ty_function" **)
val start : t -> ty_module -> ty_function -> unit

(** pause the timer "ty_module x ty_function" and restore the former timer **)
val pause : t -> ty_module -> ty_function -> unit

(** update the value of the current timer **)
val update : t -> unit

(** get the value of the timer "ty_module x ty_function" **)
val get_value : t -> ty_module -> ty_function -> float

(** get the sum of the "ty_function" timers for the given "ty_module" **)
val get_sum : t -> ty_module -> float

val current_timer : t -> ty_module * ty_function * int

val string_of_ty_module : ty_module -> string

val string_of_ty_function : ty_function -> string

val get_stack : t -> (ty_module * ty_function * int) list

val all_modules : ty_module list

val all_functions : ty_function list

(** This functions assumes (asserts) that timers() yields true **)
val set_timer_start : (ty_module -> ty_function -> unit) -> unit

(** This functions assumes (asserts) that timers() yields true **)
val set_timer_pause : (ty_module -> ty_function -> unit) -> unit

val with_timer : ty_module -> ty_function -> (unit -> 'a) -> 'a
(** [with_timer mod_ fun_ f] wraps the call [f ()] with the timer
    [(mod_, fun_)]. *)
