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

val src : Logs.src

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
    Util.matching_env -> t -> (Expr.t * int * Explanation.t) Expr.Map.t -> t
  val terms_info : t -> info Expr.Map.t * Expr.t list Expr.Map.t Symbols.Map.t
  val query :
    Util.matching_env -> t -> theory -> (trigger_info * gsubst list) list

  val reinit_caches : unit -> unit
  (** Empties the e-matching caches *)

end


module type Arg = sig
  type t
  val term_repr : t -> Expr.t -> init_term:bool -> Expr.t
  val are_equal : t -> Expr.t -> Expr.t -> init_terms:bool -> Th_util.answer
  val class_of : t -> Expr.t -> Expr.Set.t
end


module Make (X : Arg) : S with type theory = X.t
