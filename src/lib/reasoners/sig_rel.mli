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

type 'a literal = 'a Xliteral.view Literal.view

type instances = (Expr.t list * Expr.gformula * Explanation.t) list

type 'a input =
  'a Xliteral.view * Expr.t option * Explanation.t * Th_util.lit_origin

type 'a fact = 'a literal * Explanation.t * Th_util.lit_origin

type 'a facts = {
  equas     : 'a fact Queue.t;
  diseqs  : 'a fact Queue.t;
  ineqs   : 'a fact Queue.t;
  mutable touched : 'a Util.MI.t;
}

type 'a result = {
  assume: 'a fact list;
  remove: Expr.t list;
}

module type RELATION = sig
  type t

  val src : Logs.src

  val timer : Timers.ty_module

  val empty : Uf.t -> t * Uf.GlobalDomains.t
  (** [empty uf] creates a new environment for this relation and allows for the
      registration of global domains in the union-find.

      The second component of the pair should be [Uf.domains uf] with any
      domains that the relation requires added. *)

  val assume : t ->
    Uf.t -> (Shostak.Combine.r input) list ->
    t * Uf.GlobalDomains.t * Shostak.Combine.r result
  (** [assume env uf la] adds and processes the literals in [la] to the
      environment [env].

      The second value returned by this function can be used to update any
      relevant domain. *)

  val query  : t -> Uf.t -> Shostak.Combine.r input -> Th_util.answer

  val case_split :
    t -> Uf.t -> for_model:bool -> Th_util.case_split list
  (** case_split env returns a list of equalities

      The returned case splits *must* have a [CS] origin; see the doc of
      [Th_util.case_split].

      The [for_model] flag is [true] when we are splitting for the purpose of
      generating a model; the case split may need to be more aggressive in this
      case to ensure completeness.

      Note: not always equalities (e.g. the arrays theory returns
      disequalities) *)

  val optimizing_objective :
    t -> Uf.t -> Objective.Function.t -> Th_util.optimized_split option
  (** [optimizing_split env uf o] tries to optimize objective [o].
      Returns [None] if the theory cannot optimize the objective. *)

  val add : t -> Uf.t -> Shostak.Combine.r -> Expr.t ->
    t * Uf.GlobalDomains.t *
    (Shostak.Combine.r Xliteral.view * Explanation.t) list
  (** add a representant to take into account *)

  val instantiate :
    do_syntactic_matching:bool ->
    Matching_types.info Expr.Map.t * Expr.t list Expr.Map.t Symbols.Map.t ->
    t -> Uf.t -> (Expr.t -> Expr.t -> bool) ->
    t * instances

  val new_terms : t -> Expr.Set.t
  (** [new_terms env] returns all the new terms created by the theory.
      These terms can be used to instantiate axiomes. *)

  val assume_th_elt : t -> Expr.th_elt -> Explanation.t -> t

end
