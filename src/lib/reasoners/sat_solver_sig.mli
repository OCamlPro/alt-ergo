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

type timeout_reason =
  | Assume
  | ProofSearch
  | ModelGen

type unknown_reason =
  | Incomplete
  | Memout
  | Step_limit of int
  | Timeout of timeout_reason

val pp_smt_unknown_reason: unknown_reason Fmt.t
(** Prints the unknown reason in the default SMT-LIB format. *)

val pp_ae_unknown_reason_opt : unknown_reason option Fmt.t
(** Prints an optional unknown reason in Alt-Ergo format. *)

module type S = sig
  type t

  exception Sat
  exception Unsat of Explanation.t
  exception I_dont_know

  val empty : ?selector:(Expr.t -> bool) -> unit -> t
  (** [empty ~selector ()] creates an empty environment.

      The optional argument [selector] is used to filter ground facts
      discovered by the instantiation engine. *)

  val declare : t -> ModelMap.profile -> unit
  (** [declare env id] declares a new identifier [id].

      If the environment [env] is not unsatisfiable and the model generation
      is enabled, the solver produces a model term for [id] which can be
      retrieved with [get_model]. *)

  val push : t -> int -> unit
  (** [push env n] adds [n] new assertion levels in [env].

      Internally, for each new assertion level, a fresh guard [g] is created
      and all formulas [f] assumed at this assertion level is replaced by
      [g ==> f].

      The guard [g] is forced to be [true] but not propagated at level [0]. *)

  val pop : t -> int -> unit
  (** [pop env n] removes [n] assertion levels in [env].

      Internally, the guard [g] introduced in [push] corresponding to this pop
      is propagated to [false] at level [0].

      @raise Errors.Error if there is no [n] assertion levels in [env]. *)

  val assume : t -> Expr.gformula -> Explanation.t -> unit
  (** [assume env f dep] assumes the ground formula [f] in [env].
      The [dep] argument can be used to generate an unsat core.

      @raise Unsat if [f] is unsatisfiable in [env]. *)

  val assume_th_elt : t -> Expr.th_elt -> Explanation.t -> unit
  (** [assume env f exp] assumes a new formula [f] with the explanation [exp]
      in the theory environment of [env]. *)

  val pred_def : t -> Expr.t -> string -> Explanation.t -> Loc.t -> unit
  (** [pred_def env f] assumes a new predicate definition [f] in [env]. *)

  val optimize : t -> Objective.Function.t -> unit
  (** [optimize env fn] registers the objective function [fn].

      After optimization, the value of this objective is returned by
      [get_objectives]. *)

  val unsat : t -> Expr.gformula -> Explanation.t
  (** [unsat env f] checks the unsatisfiability of [f] in [env].

      @raise I_dont_know if the solver cannot prove the unsatisfiability
             of [env].
      @raise Sat if [f] is satisfiable in [env]. *)

  val reset_refs : unit -> unit

  val reinit_ctx : unit -> unit
  (** [reinit_ctx ()] reinitializes the solving context. *)

  val get_model: t -> Models.t option
  (** [get_model t] produces the current first-order model.
      Notice that this model is a best-effort.

      @return [None] if the model generation is not enabled or the
      environment is unsatisfiable. *)

  val get_unknown_reason : t -> unknown_reason option
  (** [get_unknown_reason t] returns the reason Alt-Ergo raised
      [I_dont_know] if it did. If it did not, returns [None]. *)

  val get_value : t -> Expr.t -> Expr.t option
  (** [get_value t e] returns the value of [e] as a constant expression
      in the current model generated. Returns [None] if can't decide. *)

  val get_objectives : t -> Objective.Model.t option
  (** [get_objectives t] returns the current objective values.

      @return [None] if there is no objective or the environment is
      unsatisfiable. *)

  val supports_optimization : bool
  (** Returns whether the solver supports optimization. *)
end


module type SatContainer = sig
  val src : Logs.src

  module Make (_ : Theory.S) : S
end
