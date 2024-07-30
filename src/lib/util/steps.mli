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

(** Module_Name

    This module aims to count the number of steps in the theories used to solve
    the problem.
*)

(** {1 Steps counters} *)

type incr_kind =
    Matching          (** Matching step increment *)
  | Interval_Calculus (** Arith : Interval Calculus increment *)
  | Fourier           (** Arith : FourierMotzkin step increment *)
  | Omega             (** Arith : number of omega procedure on  Real and Int *)
  | Uf                (** UF step increment *)
  | Ac                (** AC step reasoning *)
  | CP                (** Constraint propagation *)
  | Th_assumed of int (** Increment the counter for each term assumed in the
                          theories environment *)
(** Define the type of increment *)

(** Returns the max number of bounds *)
val get_steps_bound : unit -> int

(** Sets the max number of bounds *)
val set_steps_bound : int -> unit

val incr  : incr_kind -> unit
(** Increment the number of steps depending of the incr_kind
    @raise Errors.Error.Invalid_steps_count if the number of steps is inbound
    by the --steps-bound option.
    @raise Run_error
    {!Errors.Invalid_steps_count} if the number of steps sent to the theories
     is invalid.
    @raise {!Util.Step_limit_reached} if the number of steps is reached *)

val reset_steps : unit -> unit
(** Reset the global steps counter *)

val save_steps : unit -> unit
(** Saves the step counters *)

val reinit_steps : unit -> unit
(** Reinitializes the step counters *)

val get_steps : unit -> int
(** Return the number of steps *)

(** Return the number of case-split steps *)
val cs_steps : unit -> int

(** Increase the number of case-split steps *)
val incr_cs_steps : unit -> unit

(** Disables the step limit during the execution of the continuation. *)
val apply_without_step_limit : (unit -> 'a) -> 'a

(** {2 Incrementality} *)

val push_steps : unit -> unit
(** Save all the steps value in an internal stack for each push command *)

val pop_steps : unit -> unit
(** Pop the last steps value when a pop command is processed *)
