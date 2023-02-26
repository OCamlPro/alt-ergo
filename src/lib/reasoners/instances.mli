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

(** type module of the module of instanciation. *)
module type S = sig
  type t
  (** Type of the environment of the instanciation. *)

  type tbox
  type instances = (Expr.gformula * Explanation.t) list

  val empty : t
  (** The initial environment. *)

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
    selector:(Expr.t -> Expr.t -> bool) ->
    ilvl:int ->
    instances * instances (* goal_directed, others *)

  val m_predicates :
    Util.matching_env ->
    t ->
    tbox ->
    selector:(Expr.t -> Expr.t -> bool) ->
    ilvl:int ->
    instances * instances (* goal_directed, others *)

  val register_max_term_depth : t -> int -> t
  (** [register_max_term_depth env i] increases the size of the environment
      used in the e-matching procedure. See {!val Matching.max_term_depth} for
      more details. *)

  val get_maching_env : t -> Matching.env

end

module Make (X : Theory.S) : S with type tbox = X.t
