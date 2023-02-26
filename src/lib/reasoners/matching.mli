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

type subst = {
  content : Expr.Subst.t;
  age : int;
  lemma_orig : Expr.t;
  terms_orig : Expr.t list;
  from_goal : bool;
}

type term_info = {
  age : int;
  lemmas_orig : Expr.t list;
  terms_orig : Expr.t list;
  from_goal : bool;
}

type trigger_info = {
  age : int;
  lemma_orig : Expr.t;
  formula_orig : Expr.t;
  dep : Explanation.t;
  increm_guard : Expr.t;
}

type env

(** Module type returned by the functor {!module:Make}. *)
module type S = sig
  (** {1 Types} *)

  type t = env
  (** Type of the environment of the e-matching. *)

  type theory

  (** {1 Constructors} *)

  val make : int -> t
  (** An initial environment. *)

  val clean_triggers : t -> t
  (** [make ~max_t_depth e trs] create a new environment. *)

  val add_term :
    t ->
    age:int ->
    from_goal:bool ->
    ?lemma_orig:Expr.t ->
    terms_orig:Expr.t list ->
    Expr.t ->
    t
  (** [add_term info e env] add the term [e] and its subterms to
      the environment [env]. *)

  val max_term_depth : t -> int -> t
  (** [max_term_depth env i] change the maximum of depth visiting if
      the value [i] is larger than the previous value. *)

  val add_triggers :
    Util.matching_env ->
    (int * Expr.t * Explanation.t) Expr.Map.t ->
    t ->
    t
  (** [add_triggers mconf env lemmas] add to the environment [env] the
      triggers contained in the formulas [lemmas].
      More precisely, [formulas] is a map of lemmas to triplets
      (age, increm_guard, dep) where [age] is the initial [age]
      of the new trigger. *)

  val query :
    Util.matching_env ->
    t ->
    theory ->
    (Expr.trigger * trigger_info * subst list) list

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
