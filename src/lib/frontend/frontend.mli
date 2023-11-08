(**************************************************************************)
(*                                                                        *)
(*     Alt-Ergo: The SMT Solver For Software Verification                 *)
(*     Copyright (C) 2013-2023 --- OCamlPro SAS                           *)
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
(*     Until 2013, some parts of this code were released under            *)
(*     the Apache Software License version 2.0.                           *)
(*                                                                        *)
(*     ---------------------------------------------------------------    *)
(*                                                                        *)
(*     More details can be found in the directory licenses/               *)
(*                                                                        *)
(**************************************************************************)

type used_context

val init_all_used_context : unit -> used_context
val choose_used_context : used_context -> goal_name:string -> used_context

type 'a status =
  | Unsat of Commands.sat_tdecl * Explanation.t
  | Inconsistent of Commands.sat_tdecl
  | Sat of Commands.sat_tdecl * 'a
  | Unknown of Commands.sat_tdecl * 'a
  | Timeout of Commands.sat_tdecl option
  | Preprocess

val print_status : 'a status -> int -> unit

module type S = sig

  (** The SAT working environment. *)
  type sat_env

  type res = [
    | `Sat of sat_env
    | `Unknown of sat_env
    | `Unsat
  ]

  type env = {
    used_context : used_context;
    consistent_dep_stack: (res * Explanation.t) Stack.t;
    sat_env : sat_env;
    res : res;
    expl : Explanation.t
  }

  type 'a process = ?loc:Loc.t -> env -> 'a -> env

  val init_env : ?sat_env:sat_env -> used_context -> env

  val push : int process

  val pop : int process

  val assume : (string * Expr.t * bool) process

  val pred_def : (string * Expr.t) process

  val query : (string * Expr.t * Ty.goal_sort) process

  val th_assume : Expr.th_elt process

  val process_decl:
    ?hook_on_status:(sat_env status -> int -> unit) ->
    env ->
    Commands.sat_tdecl ->
    env
end

module Make (SAT: Sat_solver_sig.S) : S with type sat_env = SAT.t

val unknown_reason_to_string : Sat_solver_sig.unknown_reason -> string
