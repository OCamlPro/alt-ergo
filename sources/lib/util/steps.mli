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
  | Th_assumed of int (** Increment the counter for each term assumed in the
                          theories environment *)
(** Define the type of increment *)

val incr  : incr_kind -> unit
(** Increment the number of steps depending of the incr_kind
    and check if the number of steps is inbound by the -steps-bound option.
    Exit if the number of steps is reached *)

val reset_steps : unit -> unit
(** Reset the global steps counter *)

val get_steps : unit -> int
(** Return the number of steps *)
