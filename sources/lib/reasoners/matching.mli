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
  type theory
  open Matching_types

  val empty : t

  val make:
    max_t_depth:int ->
    Matching_types.info Expr.Map.t ->
    Expr.t list Expr.Map.t Symbols.Map.t ->
    Matching_types.trigger_info list ->
    t

  val add_term : term_info -> Expr.t -> t -> t
  val max_term_depth : t -> int -> t
  val add_triggers :
    Util.matching_env -> t -> (int * Explanation.t) Expr.Map.t -> t
  val terms_info : t -> info Expr.Map.t * Expr.t list Expr.Map.t Symbols.Map.t
  val query :
    Util.matching_env -> t -> theory -> (trigger_info * gsubst list) list

end


module type Arg = sig
  type t
  val term_repr : t -> Expr.t -> init_term:bool -> Expr.t
  val are_equal : t -> Expr.t -> Expr.t -> init_terms:bool -> Th_util.answer
  val class_of : t -> Expr.t -> Expr.t list
end


module Make (X : Arg) : S with type theory = X.t
