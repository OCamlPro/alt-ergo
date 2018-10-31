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

module type S = sig

  type sat_env

  type used_context

  type status =
    | Unsat of Commands.sat_tdecl * Explanation.t
    | Inconsistent of Commands.sat_tdecl
    | Sat of Commands.sat_tdecl * sat_env
    | Unknown of Commands.sat_tdecl * sat_env
    | Timeout of Commands.sat_tdecl option
    | Preprocess

  val process_decl:
    (status -> int64 -> unit) ->
    used_context ->
    sat_env * bool * Explanation.t -> Commands.sat_tdecl ->
    sat_env * bool * Explanation.t

  val print_status : status -> int64 -> unit

  val init_all_used_context : unit -> used_context
  val choose_used_context : used_context -> goal_name:string -> used_context

end

module Make (SAT: Sat_solver_sig.S) : S with type sat_env = SAT.t
