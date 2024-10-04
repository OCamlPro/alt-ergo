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

type used_context

val init_all_used_context : unit -> used_context
val choose_used_context : used_context -> goal_name:string -> used_context

type status =
  | Unsat of Commands.sat_tdecl * Explanation.t
  | Inconsistent of Commands.sat_tdecl
  | Sat of Commands.sat_tdecl
  | Unknown of Commands.sat_tdecl
  | Timeout of Commands.sat_tdecl option
  | Preprocess

val print_status : status -> int -> unit

module type S = sig

  (** The SAT working environment. *)
  type sat_env

  type res = [
    | `Sat
    | `Unknown
    | `Unsat
  ]

  type env = private {
    used_context : used_context;
    consistent_dep_stack: (res * Explanation.t) Stack.t;
    sat_env : sat_env;
    mutable res : res;
    mutable expl : Explanation.t
  }

  val init_env : ?selector_inst:(Expr.t -> bool) -> used_context -> env

  (** Process are wrappers of calls to the SAT solver.
      They catch the [Sat], [Unsat] and [I_dont_know] exceptions to update the
      frontend environment, but not the [Timeout] exception which is raised to
      the user. *)
  type 'a process = ?loc:Loc.t -> 'a -> env -> unit

  val push : int process

  val pop : int process

  val assume : (string * Expr.t * bool) process

  val pred_def : (string * Expr.t) process

  val query : (string * Expr.t * Ty.goal_sort) process

  val th_assume : Expr.th_elt process

  val optimize : Objective.Function.t process

  val process_decl:
    ?hook_on_status:(status -> int -> unit) ->
    env ->
    Commands.sat_tdecl ->
    unit

  val print_model: sat_env Fmt.t
end

module Make (SAT: Sat_solver_sig.S) : S with type sat_env = SAT.t
