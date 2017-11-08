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
(*     Copyright (C) 2013-2017 --- OCamlPro SAS                               *)
(*                                                                            *)
(*     This file is distributed under the terms of the Apache Software        *)
(*     License version 2.0                                                    *)
(*                                                                            *)
(******************************************************************************)

open Typed

module type S = sig

  type sat_env

  type output = Unsat of Explanation.t | Inconsistent
	        | Sat of sat_env | Unknown of sat_env

  val process_decl:
    (Commands.sat_tdecl -> output -> int64 -> unit) ->
    sat_env * bool * Explanation.t -> Commands.sat_tdecl ->
    sat_env * bool * Explanation.t

  val typecheck_file :
    Parsed.file ->
    ((int tdecl, int) annoted * Typechecker.env) list list

  val print_status : Commands.sat_tdecl -> output -> int64 -> unit
end

module Make (SAT: Sat_solver_sig.S) : S with type sat_env = SAT.t
