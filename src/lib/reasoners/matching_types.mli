(******************************************************************************)
(*                                                                            *)
(*  Alt-Ergo: The SMT Solver For Software Verification                        *)
(*  Copyright (C) --- OCamlPro SAS                                            *)
(*                                                                            *)
(*  This software is governed by the CeCILL  license under French law and     *)
(*  abiding by the rules of distribution of free software.  You can  use,     *)
(*  modify and/ or redistribute the software under the terms of the CeCILL    *)
(*  license as circulated by CEA, CNRS and INRIA at the following URL         *)
(*  "http://www.cecill.info".                                                 *)
(*                                                                            *)
(*  As a counterpart to the access to the source code and  rights to copy,    *)
(*  modify and redistribute granted by the license, users are provided only   *)
(*  with a limited warranty  and the software's author,  the holder of the    *)
(*  economic rights,  and the successive licensors  have only  limited        *)
(*  liability.                                                                *)
(*                                                                            *)
(*  In this respect, the user's attention is drawn to the risks associated    *)
(*  with loading,  using,  modifying and/or developing or reproducing the     *)
(*  software by the user in light of its specific status of free software,    *)
(*  that may mean  that it is complicated to manipulate,  and  that  also     *)
(*  therefore means  that it is reserved for developers  and  experienced     *)
(*  professionals having in-depth computer knowledge. Users are therefore     *)
(*  encouraged to load and test the software's suitability as regards their   *)
(*  requirements in conditions enabling the security of their systems and/or  *)
(*  data to be ensured and,  more generally, to use and operate it in the     *)
(*  same conditions as regards security.                                      *)
(*                                                                            *)
(*  The fact that you are presently reading this means that you have had      *)
(*  knowledge of the CeCILL license and that you accept its terms.            *)
(*                                                                            *)
(*  ------------------------------------------------------------------------  *)
(*                                                                            *)
(*  This is a free release of Alt-Ergo under the terms of CeCILL license.     *)
(*  The latest releases of Alt-Ergo are distributed under the terms of        *)
(*  OCamlPro Non-Commercial Purpose License, version 1.                       *)
(*                                                                            *)
(*  ------------------------------------------------------------------------  *)
(*                                                                            *)
(*  The Alt-Ergo theorem prover                                               *)
(*                                                                            *)
(*  Sylvain Conchon, Evelyne Contejean, Francois Bobot                        *)
(*  Mohamed Iguernelala, Stephane Lescuyer, Alain Mebsout                     *)
(*                                                                            *)
(*  CNRS - INRIA - Universite Paris Sud                                       *)
(*                                                                            *)
(*  ------------------------------------------------------------------------  *)
(*                                                                            *)
(*  More details can be found in the directory licenses/                      *)
(*                                                                            *)
(******************************************************************************)

type gsubst = {
  sbs : Expr.t Symbols.Map.t;
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
