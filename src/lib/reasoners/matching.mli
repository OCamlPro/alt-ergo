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

(** Module type returned by the functor {!module:Make}. *)
module type S = sig
  (** {1 Types} *)

  type t
  (** Type of the environment of the e-matching. *)

  type theory
  open Matching_types

  (** {1 Constructors} *)

  val empty : t
  (** An initial environment. *)

  val make :
    max_t_depth: int ->
    known_terms: Expr.Set.t ->
    known_pats: Expr.trigger list ->
    Expr.Set.t Symbols.Map.t ->
    t
  (** [make ~max_t_depth e trs] create a new environment. *)

  val add_term : t -> Expr.t -> t
  (** [add_term info e env] add the term [e] and its subterms to
      the environment [env]. *)

  val max_term_depth : t -> int -> t
  (** [max_term_depth env i] change the maximum of depth visiting if
      the value [i] is larger than the previous value. *)

  val add_triggers :
    Util.matching_env -> t -> Expr.t list -> t

  val query :
    Util.matching_env -> t -> theory -> Expr.Subst.t list list

end


module type Arg = sig
  type t
  (** Type of the union-find environment. *)

  val term_repr : t -> Expr.t -> init_term:bool -> Expr.t
  (** [term_repr env e ~init_term] return the current representant of the term
      [e] in the union-find environment [env]. The argument [init_term] is used
      by the Ccx module to add the term [e] to its environment. *)

  val are_equal : t -> Expr.t -> Expr.t -> init_terms:bool -> Th_util.answer
  (** [are_equal env e1 e2 ~init_terms] check if the terms [e1] and [e2] are
      equal. The argument [init_terms] is used by the Ccx module to add the
      terms [e1] and [e2] to its environment. *)

  val class_of : t -> Expr.t -> Expr.t list
  (** [class_of env e] return the class of the term [e] in the
      union-find environment [env]. *)
end

(** Functor who builds the e-matching module from the union-find structure. *)
module Make (X : Arg) : S with type theory = X.t
