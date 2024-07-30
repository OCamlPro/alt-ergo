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

type gsubst = {
  sbs : Expr.t Var.Map.t;
  sty : Ty.subst;
  gen : int ;     (* l'age d'une substitution est l'age du plus vieux
                     		     terme qu'elle contient *)
  goal : bool;    (* vrai si la substitution contient un terme ayant un lien
                     		     avec le but de la PO *)
  s_term_orig : Expr.t list;
  s_lem_orig : Expr.t;
}

type trigger_info = {
  trigger : Expr.trigger;
  trigger_age : int ;  (* age d'un trigger *)
  trigger_orig : Expr.t ; (* lemme d'origine *)
  trigger_formula : Expr.t ; (* formule associee au trigger *)
  trigger_dep : Explanation.t ;
  trigger_increm_guard : Expr.t
  (* guard associated to push in incremental mode *)
}

type term_info = {
  term_age : int ;        (* age du terme *)
  term_from_goal : bool ;   (* vrai si le terme provient du but de la PO *)
  term_from_formula : Expr.t option; (* lemme d'origine du terme *)
  term_from_terms : Expr.t list;
}

type info = {
  age : int ; (* age du terme *)
  lem_orig : Expr.t list ; (* lemme d'ou provient eventuellement le terme *)
  t_orig : Expr.t list;
  but : bool  (* le terme a-t-il un lien avec le but final de la PO *)
}
