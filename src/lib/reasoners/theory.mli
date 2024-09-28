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

module type S = sig
  type t

  val empty : unit -> t

  (* the first int is the decision level (dlvl) and the second one is the
     propagation level (plvl). The facts (first argument) are sorted in
     decreasing order with respect to (dlvl, plvl) *)
  val assume :
    ?ordered:bool ->
    (Shostak.Literal.t * Th_util.lit_origin * Explanation.t * int * int) list
    -> t -> t * Expr.Set.t * int

  val add_objective :
    t -> Objective.Function.t -> Objective.Value.t -> t
  (** [add_objective env fn value] indicates that the objective [fn] has been
      optimized to [value]. *)

  val query : Expr.t -> t -> Th_util.answer
  val cl_extract : t -> Expr.Set.t list
  val extract_ground_terms : t -> Expr.Set.t
  val get_real_env : t -> Ccx.Main.t
  val get_case_split_env : t -> Ccx.Main.t
  val do_optimize :
    acts:Shostak.Literal.t Th_util.acts -> t -> unit
  val do_case_split :
    ?acts:Shostak.Literal.t Th_util.acts ->
    t -> Util.case_split_policy -> t * Expr.Set.t

  val add_term : t -> Expr.t -> add_in_cs:bool -> t

  val compute_concrete_model :
    acts:Shostak.Literal.t Th_util.acts -> t -> unit
  val extract_concrete_model :
    declared_ids:ModelMap.profile list ->
    t ->
    Models.t Lazy.t * Objective.Model.t

  val assume_th_elt : t -> Expr.th_elt -> Explanation.t -> t
  val theories_instances :
    do_syntactic_matching:bool ->
    Matching_types.info Expr.Map.t * Expr.t list Expr.Map.t Symbols.Map.t ->
    t -> (Expr.t -> Expr.t -> bool) ->
    int -> int -> t * Sig_rel.instances

  val get_assumed : t -> Expr.Set.t
  val reinit_cpt : unit -> unit
  (** Reinitializes the internal counter. *)

  val get_objectives : t -> Objective.Model.t
end

module Main_Default : S
module Main_Empty : S
