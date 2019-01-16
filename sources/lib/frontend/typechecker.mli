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

type env
(** The type of global environment of the typechecker. *)

val type_expr :
  env -> (Symbols.t * Ty.t) list -> Parsed.lexpr -> int Typed.atterm
(** Typecheck an input expression (i.e. term (or formula ?)), given
    a local environment and a list of local types used to extend the
    initial environment. *)
(* TODO: give the env a proper module with binding functions,
         so that the list argument can be ommitted ? *)

val type_file : Parsed.file -> (int Typed.atdecl * env) list * env
(** Type an input file. Returns the successive global environments
    obtained after typing each declaration. *)


(* TODO: move these 2 functiosn out of the typechecker *)
(* two functions split_goals to minimize useless changes in the GUI *)

(* used by main_gui *)
val split_goals :
  (int Typed.atdecl * 'a) list ->
  ((int Typed.atdecl * 'a) list * string) list

(* used by main_text *)
val split_goals_and_cnf :
  (int Typed.atdecl * 'a) list ->
  (Commands.sat_tdecl list * string) list

