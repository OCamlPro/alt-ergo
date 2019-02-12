(******************************************************************************)
(*                                                                            *)
(*     The Alt-Ergo theorem prover                                            *)
(*     Copyright (C) 2006-2013                                                *)
(*                                                                            *)
(*     Sylvain Conchon                                                        *)
(*     Evelyne Contejean                                                      *)
(*                                                                            *)
(*     Francois Bobot                                                         *)
(*     Mohamed Iguernelala                                                    *)
(*     Stephane Lescuyer                                                      *)
(*     Alain Mebsout                                                          *)
(*                                                                            *)
(*     CNRS - INRIA - Universite Paris Sud                                    *)
(*                                                                            *)
(*     This file is distributed under the terms of the Apache Software        *)
(*     License version 2.0                                                    *)
(*                                                                            *)
(*  ------------------------------------------------------------------------  *)
(*                                                                            *)
(*     Alt-Ergo: The SMT Solver For Software Verification                     *)
(*     Copyright (C) 2013-2018 --- OCamlPro SAS                               *)
(*                                                                            *)
(*     This file is distributed under the terms of the Apache Software        *)
(*     License version 2.0                                                    *)
(*                                                                            *)
(******************************************************************************)

type ty_module =
  | M_None
  | M_Typing
  | M_Sat
  | M_Match
  | M_CC
  | M_UF
  | M_Arith
  | M_Arrays
  | M_Sum
  | M_Records
  | M_AC
  | M_Expr
  | M_Triggers
  | M_Simplex

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

val get_timers_array : t -> (float array) array

val mtag : ty_module -> int

val ftag : ty_function -> int

val all_modules : ty_module list

val all_functions : ty_function list

(** This functions assumes (asserts) that timers() yields true **)
val set_timer_start : (ty_module -> ty_function -> unit) -> unit

(** This functions assumes (asserts) that timers() yields true **)
val set_timer_pause : (ty_module -> ty_function -> unit) -> unit

val exec_timer_start : ty_module -> ty_function -> unit
val exec_timer_pause : ty_module -> ty_function -> unit
