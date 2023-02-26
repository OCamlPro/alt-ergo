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

(** This module defined annotated substitutions, triggers and terms used by the
    e-matching module. *)

type gsubst = {
  sbs : Expr.Subst.t;
  (** The annotated substitution. *)

  age : int;
  (** The age of the substition which is the age of the oldest term in it. *)

  from_goal : bool;
  (* vrai si la substitution contient un terme ayant un lien
                     		     avec le but de la PO *)

  s_term_orig : Expr.t list;

  s_lem_orig : Expr.t;
}
(** Type of an annotated ground substitution. *)

type trigger_info = {
  trigger : Expr.trigger;
  (** The annotated trigger. *)

  trigger_age : int;
  (** The age of the trigger. *)

  trigger_orig : Expr.t;
  (** The lemma in which the trigger has been defined. *)

  trigger_formula : Expr.t;
  (* formule associee au trigger *)

  trigger_dep : Explanation.t;
  (** The explanation of the trigger. *)

  trigger_increm_guard : Expr.t;
  (** Guard associated to push in incremental mode. *)
}
(** Type of an annotated trigger. *)

type term_info = {
  term_age : int;
  (** age du terme. *)

  term_from_goal : bool;
  (* vrai si le terme provient du but de la PO *)

  term_from_formula : Expr.t option;
  (* lemme d'origine du terme *)

  term_from_terms : Expr.t list;
}
(** Type of the term information. *)

type info = {
  age : int;
  (** Age of the term. *)

  lem_orig : Expr.t list;
  (* lemme d'ou provient eventuellement le terme *)

  t_orig : Expr.t list;

  from_goal : bool;
  (* le terme a-t-il un lien avec le but final de la PO *)
}
