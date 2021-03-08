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

type 'a literal = LTerm of Expr.t | LSem of 'a Xliteral.view

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
  assume : 'a fact list;
  remove: Expr.t list;
}

type case_split =
  | Split of Th_util.split_info list
  | Optimized_split of Th_util.optimized_split

module type RELATION = sig
  type t

  val empty : Expr.Set.t list -> t

  val assume : t ->
    Uf.t -> (Shostak.Combine.r input) list -> t * Shostak.Combine.r result
  val query  : t -> Uf.t -> Shostak.Combine.r input -> Th_util.answer

  val case_split :
    t -> Uf.t ->
    for_model:bool ->
    to_optimize: Th_util.optimized_split option ->
    case_split
  (** case_split env returns a list of equalities *)

  val add : t -> Uf.t -> Shostak.Combine.r -> Expr.t ->
    t * (Shostak.Combine.r Xliteral.view * Explanation.t) list
  (** add a representant to take into account *)

  val instantiate :
    do_syntactic_matching:bool ->
    Matching_types.info Expr.Map.t * Expr.t list Expr.Map.t Symbols.Map.t ->
    t -> Uf.t -> (Expr.t -> Expr.t -> bool) ->
    t * instances

  val new_terms : t -> Expr.Set.t

  val assume_th_elt : t -> Expr.th_elt -> Explanation.t -> t

end
