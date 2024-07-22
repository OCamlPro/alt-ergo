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

type env
(** The type of global environment of the typechecker. *)

val empty_env : env
(** The empty/initial environment *)

val type_expr :
  env -> (Symbols.t * Ty.t) list -> Parsed.lexpr -> int Typed.atterm
(** Typecheck an input expression (i.e. term (or formula ?)), given
    a local environment and a list of local types used to extend the
    initial environment.
    @raise Typing_error {!Errors.Typing_error} *)
(* TODO: give the env a proper module with binding functions,
         so that the list argument can be ommitted ? *)

val type_parsed :
  env -> env Stack.t -> Parsed.decl -> int Typed.atdecl list * env
(** Type a single declaration.
    @raise Typing_error {!Errors.Typing_error} *)

val type_file : Parsed.file -> (int Typed.atdecl * env) list * env
(** Type an input file. Returns the successive global environments
    obtained after typing each declaration.
    @raise Typing_error {!Errors.Typing_error} *)


(* TODO: move these functions out of the typechecker *)
(* used by main_gui *)
val split_goals :
  (int Typed.atdecl * 'a) list ->
  ((int Typed.atdecl * 'a) list * string) list

(* exported for compat with lib_usage.ml *)
val split_goals_and_cnf :
  (int Typed.atdecl * 'a) list ->
  (Commands.sat_tdecl list * string) list

