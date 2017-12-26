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

  val empty : unit -> t

  (* the first int is the decision level (dlvl) and the second one is the
     propagation level (plvl). The facts (first argument) are sorted in
     decreasing order with respect to (dlvl, plvl) *)
  val assume :
    ?ordered:bool ->
    (Literal.LT.t * Explanation.t * int * int) list -> t ->
    t * Term.Set.t * int

  val query : Literal.LT.t -> t -> Sig.answer
  val class_of : t -> Term.t -> Term.t list
  val are_equal : t -> Term.t -> Term.t -> add_terms:bool -> Sig.answer
  val print_model : Format.formatter -> t -> unit
  val cl_extract : t -> Term.Set.t list
  val term_repr : t -> Term.t -> Term.t
  val extract_ground_terms : t -> Term.Set.t
  val get_real_env : t -> Ccx.Main.t
  val get_case_split_env : t -> Ccx.Main.t
  val do_case_split : t -> t * Term.Set.t
  val add_term : t -> Term.t -> add_in_cs:bool -> t

  val compute_concrete_model : t -> t

  val assume_th_elt : t -> Commands.th_elt -> t
  val theories_instances :
    do_syntactic_matching:bool ->
    Matching_types.info Term.Map.t * Term.t list Term.Map.t Term.Subst.t ->
    t -> (Formula.t -> Formula.t -> bool) ->
    int -> int -> t * Sig.instances

  val retrieve_used_context :
    t -> Explanation.t -> Formula.t list * Formula.t list

  val get_assumed : t -> (Literal.LT.t * int * int) list list
end

module Main : S
