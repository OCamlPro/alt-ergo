(*********************************************************************************)
(*                                                                               *)
(*     Alt-Ergo: The SMT Solver For Software Verification                        *)
(*     Copyright (C) --- OCamlPro SAS                                            *)
(*                                                                               *)
(*     This software is governed by the CeCILL  license under French law and     *)
(*     abiding by the rules of distribution of free software.  You can  use,     *)
(*     modify and/ or redistribute the software under the terms of the CeCILL    *)
(*     license as circulated by CEA, CNRS and INRIA at the following URL         *)
(*     "http://www.cecill.info".                                                 *)
(*                                                                               *)
(*     As a counterpart to the access to the source code and  rights to copy,    *)
(*     modify and redistribute granted by the license, users are provided only   *)
(*     with a limited warranty  and the software's author,  the holder of the    *)
(*     economic rights,  and the successive licensors  have only  limited        *)
(*     liability.                                                                *)
(*                                                                               *)
(*     In this respect, the user's attention is drawn to the risks associated    *)
(*     with loading,  using,  modifying and/or developing or reproducing the     *)
(*     software by the user in light of its specific status of free software,    *)
(*     that may mean  that it is complicated to manipulate,  and  that  also     *)
(*     therefore means  that it is reserved for developers  and  experienced     *)
(*     professionals having in-depth computer knowledge. Users are therefore     *)
(*     encouraged to load and test the software's suitability as regards their   *)
(*     requirements in conditions enabling the security of their systems and/or  *)
(*     data to be ensured and,  more generally, to use and operate it in the     *)
(*     same conditions as regards security.                                      *)
(*                                                                               *)
(*     The fact that you are presently reading this means that you have had      *)
(*     knowledge of the CeCILL license and that you accept its terms.            *)
(*                                                                               *)
(*     ------------------------------------------------------------------------  *)
(*                                                                               *)
(*     This is a free release of Alt-Ergo under the terms of CeCILL license.     *)
(*     The latest releases of Alt-Ergo are distributed under the terms of        *)
(*     OCamlPro Non-Commercial Purpose License, version 1.                       *)
(*                                                                               *)
(*     As an exception, Alt-Ergo Club members at the Gold level can              *)
(*     use this file under the terms of the Apache Software License              *)
(*     version 2.0.                                                              *)
(*                                                                               *)
(*     ------------------------------------------------------------------------  *)
(*                                                                               *)
(*     The Alt-Ergo theorem prover                                               *)
(*                                                                               *)
(*     Sylvain Conchon, Evelyne Contejean, Francois Bobot                        *)
(*     Mohamed Iguernelala, Stephane Lescuyer, Alain Mebsout                     *)
(*                                                                               *)
(*     CNRS - INRIA - Universite Paris Sud                                       *)
(*                                                                               *)
(*     ------------------------------------------------------------------------  *)
(*                                                                               *)
(*     More details can be found in the directory licenses/                      *)
(*                                                                               *)
(*********************************************************************************)

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
    @raise Errors.Error.Invalid_steps_count if the number of steps is inbound
    by the --steps-bound option.
    @raise Run_error
    {!Errors.Invalid_steps_count} if the number of steps sent to the theories
     is invalid.
    {!Errors.Steps_limit} if the number of steps is reached *)

val reset_steps : unit -> unit
(** Reset the global steps counter *)

val get_steps : unit -> int
(** Return the number of steps *)

(** Return the number of case-split steps *)
val cs_steps : unit -> int

(** Increase the number of case-split steps *)
val incr_cs_steps : unit -> unit

(** {2 Incrementality} *)

val push_steps : unit -> unit
(** Save all the steps value in an internal stack for each push command *)

val pop_steps : unit -> unit
(** Pop the last steps value when a pop command is processed *)