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
(*     Copyright (C) 2013-2017 --- OCamlPro SAS                               *)
(*                                                                            *)
(*     This file is distributed under the terms of the Apache Software        *)
(*     License version 2.0                                                    *)
(*                                                                            *)
(******************************************************************************)

module type S = sig
  type t
  type tbox
  type instances = (Formula.gformula * Explanation.t) list

  val empty : t
  val add_terms : t -> Term.Set.t -> Formula.gformula -> t
  val add_lemma : t -> Formula.gformula -> Explanation.t -> t
  val add_predicate : t -> Formula.gformula -> t

  val m_lemmas :
    backward:Util.inst_kind ->
    t ->
    tbox ->
    (Formula.t -> Formula.t -> bool) ->
    int ->
    instances * instances (* goal_directed, others *)

  val m_predicates :
    backward:Util.inst_kind ->
    t ->
    tbox ->
    (Formula.t -> Formula.t -> bool) ->
    int ->
    instances * instances (* goal_directed, others *)

  (* returns used axioms/predicates * unused axioms/predicates *)
  val retrieve_used_context :
    t -> Explanation.t -> Formula.t list * Formula.t list

  val register_max_term_depth : t -> int -> t

  val matching_terms_info :
    t -> Matching_types.info Term.Map.t * Term.t list Term.Map.t Term.Subst.t

end

module Make (X : Theory.S) : S with type tbox = X.t
