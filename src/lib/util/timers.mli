(**************************************************************************)
(*                                                                        *)
(*     Alt-Ergo: The SMT Solver For Software Verification                 *)
(*     Copyright (C) 2013-2024 --- OCamlPro SAS                           *)
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

(** environment of internal timers **)
type t

(** return a new empty env **)
val empty : unit -> t

(** reset the given env to empty *)
val reset : t -> unit

(** save the current timer and start the timer "Self.mod_ x Self.fn" **)
val start : t -> Self.mod_ -> Self.fn -> unit

(** pause the timer "Self.mod_ x Self.fn" and restore the former timer **)
val pause : t -> Self.mod_ -> Self.fn -> unit

(** update the value of the current timer **)
val update : t -> unit

(** get the value of the timer "Self.mod_ x Self.fn" **)
val get_value : t -> Self.mod_ -> Self.fn -> float

(** get the sum of the "Self.fn" timers for the given "Self.mod_" **)
val get_sum : t -> Self.mod_ -> float

val current_timer : t -> Self.mod_ * Self.fn * int

val get_stack : t -> (Self.mod_ * Self.fn * int) list

(** This functions assumes (asserts) that timers() yields true **)
val set_timer_start : (Self.mod_ -> Self.fn -> unit) -> unit

(** This functions assumes (asserts) that timers() yields true **)
val set_timer_pause : (Self.mod_ -> Self.fn -> unit) -> unit

val with_timer : Self.mod_ -> Self.fn -> (unit -> 'a) -> 'a
(** [with_timer mod_ fun_ f] wraps the call [f ()] with the timer
    [(mod_, fun_)]. *)
