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

module type S = sig
  type t
  type tbox
  type instances = (Expr.gformula * Explanation.t) list

  val empty : t
  val add_terms : t -> Expr.Set.t -> Expr.gformula -> t
  val add_lemma : t -> Expr.gformula -> Explanation.t -> t
  val add_predicate : t -> Expr.gformula -> Explanation.t -> t

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

end

module Make (X : Theory.S) : S with type tbox = X.t
