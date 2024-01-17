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

(** A functional SAT solver implementation. *)
module Make (_ : Theory.S) : sig
  type t

  exception Sat of t
  exception Unsat of Explanation.t
  exception I_dont_know of t

  val empty : ?selector:(Expr.t -> bool) -> unit -> t

  val declare : t -> Symbols.typed_name -> t

  val push : t -> int -> t

  val pop : t -> int -> t
  (** [pop env n] pops [n] assertion levels of the environment [env].

      @raise Errors.Error if there is no [n] assertion levels in [env]. *)

  val assume : t -> Expr.gformula -> Explanation.t -> t

  val assume_th_elt : t -> Expr.th_elt -> Explanation.t -> t

  val pred_def : t -> Expr.t -> string -> Explanation.t -> Loc.t -> t

  val unsat : t -> Expr.gformula -> Explanation.t

  val reset_refs : unit -> unit

  val reinit_ctx : unit -> unit

  val get_boolean_model : t -> Expr.t list

  val get_model : t -> Models.t option

  val get_unknown_reason : t -> Sat_solver_sig.unknown_reason option
end
