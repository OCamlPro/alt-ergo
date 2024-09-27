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

open Satml_types

exception Sat
exception Unsat of Satml_types.Atom.clause list option
exception Last_UIP_reason of Atom.Set.t

type conflict_origin =
  | C_none
  | C_bool of Atom.clause
  | C_theory of Explanation.t

val src : Logs.src

module type SAT_ML = sig

  (*module Make (Dummy : sig end) : sig*)
  type th
  type t

  val solve : t -> unit
  val compute_concrete_model :
    t ->
    declared_names:Symbols.typed_name list ->
    Models.t Lazy.t * Objective.Model.t

  val set_new_proxies : t -> Flat_Formula.proxies -> unit

  val new_vars :
    t ->
    nbv : int -> (* nb made vars *)
    Satml_types.Atom.var list ->
    Satml_types.Atom.atom list list -> Satml_types.Atom.atom list list ->
    Satml_types.Atom.atom list list * Satml_types.Atom.atom list list

  val assume :
    t ->
    Satml_types.Atom.atom list list ->
    Satml_types.Atom.atom list list ->
    Expr.t ->
    cnumber : int ->
    Flat_Formula.Set.t -> dec_lvl:int ->
    unit

  val boolean_model : t -> Satml_types.Atom.atom list
  val instantiation_context :
    t -> Satml_types.Flat_Formula.hcons_env -> Satml_types.Atom.Set.t
  val current_tbox : t -> th
  val set_current_tbox : t -> th -> unit
  val create : Atom.hcons_env -> t

  val assume_th_elt : t -> Expr.th_elt -> Explanation.t -> unit
  val decision_level : t -> int
  val cancel_until : t -> int -> unit

  val exists_in_lazy_cnf : t -> Flat_Formula.t -> bool
  val known_lazy_formulas : t -> int Flat_Formula.Map.t

  val reason_of_deduction: Atom.atom -> Atom.Set.t
  val assume_simple : t -> Atom.atom list list -> unit
  val do_case_split : t -> Util.case_split_policy -> conflict_origin

  val decide : t -> Atom.atom -> unit
  val conflict_analyze_and_fix : t -> conflict_origin -> unit

  val push : t -> Satml_types.Atom.atom -> unit
  val pop : t -> unit

  val optimize : t -> Objective.Function.t -> unit
  (** [optimize env fn] adds the objection [fn] to the environment
      [env].

      @raise invalid_argurment if the decision level of [env] is not zero. *)
end

module Make (Th : Theory.S) : SAT_ML with type th = Th.t
