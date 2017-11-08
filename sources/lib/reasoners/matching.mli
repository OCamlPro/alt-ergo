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
  type theory
  open Matching_types

  val empty : t

  val make:
    max_t_depth:int ->
    Matching_types.info Term.Map.t ->
    Term.t list Term.Map.t Term.Subst.t ->
    Matching_types.trigger_info list ->
    t

  val add_term : term_info -> Term.t -> t -> t
  val max_term_depth : t -> int -> t
  val add_triggers :
    backward:Util.inst_kind -> t -> (int * Explanation.t) Formula.Map.t -> t
  val terms_info : t -> info Term.Map.t * Term.t list Term.Map.t Term.Subst.t
  val query : t -> theory -> (trigger_info * gsubst list) list
  val unused_context : Formula.t -> bool

end


module type Arg = sig
  type t
  val term_repr : t -> Term.t -> Term.t
  val add_term : t -> Term.t -> t
  val are_equal : t -> Term.t -> Term.t -> add_terms:bool -> Sig.answer
  val class_of : t -> Term.t -> Term.t list
end


module Make (X : Arg) : S with type theory = X.t
