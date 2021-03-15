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

[@@@ocaml.warning "-33"]
open Options

open Sig

module type S = sig

  type t
  type r = Shostak.Combine.r

  val empty : unit -> t

  val empty_facts : unit -> r Sig_rel.facts

  val add_fact : r Sig_rel.facts -> r Sig_rel.fact -> unit

  val add_term :
    t ->
    r Sig_rel.facts -> (* acc *)
    Expr.t ->
    Explanation.t ->
    t * r Sig_rel.facts

  val add :
    t ->
    r Sig_rel.facts -> (* acc *)
    Expr.t ->
    Explanation.t -> t * r Sig_rel.facts

  val assume_literals :
    t ->
    (r Sig_rel.literal * Explanation.t * Th_util.lit_origin) list ->
    r Sig_rel.facts ->
    t * (r Sig_rel.literal * Explanation.t * Th_util.lit_origin) list

  val case_split :
    t -> for_model:bool ->
    (r Xliteral.view * bool * Th_util.lit_origin) list * t
  val query :  t -> Expr.t -> Th_util.answer
  val new_terms : t -> Expr.Set.t
  val class_of : t -> Expr.t -> Expr.t list
  val are_equal : t -> Expr.t -> Expr.t -> init_terms:bool -> Th_util.answer
  val are_distinct : t -> Expr.t -> Expr.t -> Th_util.answer
  val cl_extract : t -> Expr.Set.t list
  val term_repr : t -> Expr.t -> init_term:bool -> Expr.t
  val print_model : Format.formatter -> t -> unit
  val get_union_find : t -> Uf.t

  val assume_th_elt : t -> Expr.th_elt -> Explanation.t -> t
  val theories_instances :
    do_syntactic_matching:bool ->
    Matching_types.info Expr.Map.t * Expr.t list Expr.Map.t Symbols.Map.t ->
    t -> (Expr.t -> Expr.t -> bool) -> t * Sig_rel.instances

  val retrieve_used_context :
    t -> Explanation.t -> Expr.t list * Expr.t list
end

module Main : S
