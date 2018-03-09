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

open Parsed
open Typed

type env

val file : file ->
  ((int tdecl, int) annoted * env) list * env

(* two functions split_goals to minimize useless changes in the GUI *)

(* used by main_gui *)
val split_goals :
  ((int tdecl, int) annoted * env) list ->
  ((int tdecl, int) annoted * env) list list

(* used by main_text *)
val split_goals_and_cnf :
  ((int tdecl, int) annoted * env) list ->
  Commands.sat_tdecl list list

val term : env -> (Symbols.t * Ty.t) list -> Parsed.lexpr ->
  (int tterm, int) annoted

val new_id : unit -> int
