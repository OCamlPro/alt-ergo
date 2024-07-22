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
  type tbox
  type instances = (Expr.gformula * Explanation.t) list

  val empty : t
  val add_terms : t -> Expr.Set.t -> Expr.gformula -> t
  val add_lemma : t -> Expr.gformula -> Explanation.t -> t
  val add_predicate :
    t ->
    guard:Expr.t ->
    name:string ->
    Expr.gformula ->
    Explanation.t ->
    t

  (* the first returned expr is the guard (incremental mode),
     the second one is the defn of the given predicate *)
  val ground_pred_defn:
    Expr.t -> t -> (Expr.t * Expr.t * Explanation.t) option

  val pop : t -> guard:Expr.t -> t

  val m_lemmas :
    Util.matching_env ->
    t ->
    tbox ->
    (Expr.t -> Expr.t -> bool) ->
    int ->
    instances * instances (* goal_directed, others *)

  val m_predicates :
    Util.matching_env ->
    t ->
    tbox ->
    (Expr.t -> Expr.t -> bool) ->
    int ->
    instances * instances (* goal_directed, others *)

  val register_max_term_depth : t -> int -> t

  val matching_terms_info :
    t -> Matching_types.info Expr.Map.t * Expr.t list Expr.Map.t Symbols.Map.t

  val reinit_em_cache : unit -> unit
  (** Reinitializes the E-matching functor instance's inner cache *)

end

module Make (X : Theory.S) : S with type tbox = X.t
