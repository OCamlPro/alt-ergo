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

type timeout_reason =
  | Assume
  | ProofSearch
  | ModelGen

type unknown_reason =
  | Incomplete
  | Memout
  | Step_limit of int
  | Timeout of timeout_reason

(** Prints the unknown reason in the default SMT-LIB format *)
val pp_smt_unknown_reason: unknown_reason Fmt.t

(** Prints an optional unknown reason in Alt-Ergo format *)
val pp_ae_unknown_reason_opt : unknown_reason option Fmt.t

module type S = sig
  type t

  exception Sat
  exception Unsat of Explanation.t
  exception I_dont_know

  (** the empty sat-solver context *)
  val empty : unit -> t
  val empty_with_inst : (Expr.t -> bool) -> t

  val declare : t -> Id.typed -> unit

  (** [push env n] add n new assertion levels.
      A guard g is added for every expression e assumed at the current
      assertion level.
      Ie. assuming e after the push will become g -> e,
      a g will be forced to be true (but not propagated at level 0) *)
  val push : t -> int -> unit

  (** [pop env n] remove an assertion level.
      Internally, the guard g introduced in the push correponsding to this pop
      will be propagated to false (at level 0) *)
  val pop : t -> int -> unit

  (** [assume env f] assume a new formula [f] in [env]. Raises Unsat if
      [f] is unsatisfiable in [env] *)
  val assume : t -> Expr.gformula -> Explanation.t -> unit

  (** [assume env f exp] assume a new formula [f] with the explanation [exp]
      in the theories environment of [env]. *)
  val assume_th_elt : t -> Expr.th_elt -> Explanation.t -> unit

  (** [pred_def env f] assume a new predicate definition [f] in [env]. *)
  val pred_def : t -> Expr.t -> string -> Explanation.t -> Loc.t -> unit

  (** [optimize env ~is_max o] registers the expression [o]
      as an objective function. *)
  val optimize : t -> is_max:bool -> Expr.t -> unit

  (** [unsat env f size] checks the unsatisfiability of [f] in
      [env]. Raises I_dont_know when the proof tree's height reaches
      [size]. Raises Sat if [f] is satisfiable in [env] *)
  val unsat : t -> Expr.gformula -> Explanation.t

  (** [print_model header fmt env] print propositional model and theory model
      on the corresponding fmt. *)
  val reset_refs : unit -> unit

  (** [reinit_ctx ()] reinitializes the solving context. *)
  val reinit_ctx : unit -> unit

  (** [get_model t] produces the current model. *)
  val get_model: t -> Models.t option

  (** [get_unknown_reason t] returns the reason Alt-Ergo raised
      [I_dont_know] if it did. If it did not, returns None. *)
  val get_unknown_reason : t -> unknown_reason option

  (** [get_value t e] returns the value of [e] as a constant expression
      in the current model generated. Returns [None] if can't decide. *)
  val get_value : t -> Expr.t -> Expr.t option

  val get_objectives : t -> Objective.Model.t option
end


module type SatContainer = sig
  module Make (Th : Theory.S) : S
end
