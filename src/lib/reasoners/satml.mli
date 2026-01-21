(*********************************************************************************)
(*                                                                               *)
(*     Alt-Ergo: The SMT Solver For Software Verification                        *)
(*     Copyright (C) --- OCamlPro SAS                                            *)
(*                                                                               *)
(*     This software is governed by the CeCILL  license under French law and     *)
(*     abiding by the rules of distribution of free software.  You can  use,     *)
(*     modify and/ or redistribute the software under the terms of the CeCILL    *)
(*     license as circulated by CEA, CNRS and INRIA at the following URL         *)
(*     "http://www.cecill.info".                                                 *)
(*                                                                               *)
(*     As a counterpart to the access to the source code and  rights to copy,    *)
(*     modify and redistribute granted by the license, users are provided only   *)
(*     with a limited warranty  and the software's author,  the holder of the    *)
(*     economic rights,  and the successive licensors  have only  limited        *)
(*     liability.                                                                *)
(*                                                                               *)
(*     In this respect, the user's attention is drawn to the risks associated    *)
(*     with loading,  using,  modifying and/or developing or reproducing the     *)
(*     software by the user in light of its specific status of free software,    *)
(*     that may mean  that it is complicated to manipulate,  and  that  also     *)
(*     therefore means  that it is reserved for developers  and  experienced     *)
(*     professionals having in-depth computer knowledge. Users are therefore     *)
(*     encouraged to load and test the software's suitability as regards their   *)
(*     requirements in conditions enabling the security of their systems and/or  *)
(*     data to be ensured and,  more generally, to use and operate it in the     *)
(*     same conditions as regards security.                                      *)
(*                                                                               *)
(*     The fact that you are presently reading this means that you have had      *)
(*     knowledge of the CeCILL license and that you accept its terms.            *)
(*                                                                               *)
(*     ------------------------------------------------------------------------  *)
(*                                                                               *)
(*     This is a free release of Alt-Ergo under the terms of CeCILL license.     *)
(*     The latest releases of Alt-Ergo are distributed under the terms of        *)
(*     OCamlPro Non-Commercial Purpose License, version 1.                       *)
(*                                                                               *)
(*     As an exception, Alt-Ergo Club members at the Gold level can              *)
(*     use this file under the terms of the Apache Software License              *)
(*     version 2.0.                                                              *)
(*                                                                               *)
(*     ------------------------------------------------------------------------  *)
(*                                                                               *)
(*     The Alt-Ergo theorem prover                                               *)
(*                                                                               *)
(*     Sylvain Conchon, Evelyne Contejean, Francois Bobot                        *)
(*     Mohamed Iguernelala, Stephane Lescuyer, Alain Mebsout                     *)
(*                                                                               *)
(*     CNRS - INRIA - Universite Paris Sud                                       *)
(*                                                                               *)
(*     ------------------------------------------------------------------------  *)
(*                                                                               *)
(*     More details can be found in the directory licenses/                      *)
(*                                                                               *)
(*********************************************************************************)

open Satml_types

exception Sat
exception Unsat of Satml_types.Atom.clause list option
exception Last_UIP_reason of Atom.Set.t

type conflict_origin =
  | C_none
  | C_bool of Atom.clause
  | C_theory of Explanation.t

module type SAT_ML = sig

  (*module Make (Dummy : sig end) : sig*)
  type th
  type t

  val solve : t -> unit

  val set_new_proxies :
    t ->
    (Satml_types.Atom.atom * Satml_types.Atom.atom list * bool) Util.MI.t ->
    unit

  val new_vars :
    t ->
    nbv : int -> (* nb made vars *)
    Satml_types.Atom.var list ->
    Satml_types.Atom.atom list list -> Satml_types.Atom.atom list list ->
    Satml_types.Atom.atom list list * Satml_types.Atom.atom list list

  val assume :
    t ->
    Satml_types.Atom.atom list list ->
    Satml_types.Atom.atom list list ->
    Expr.t ->
    cnumber : int ->
    Satml_types.Atom.atom option Flat_Formula.Map.t -> dec_lvl:int ->
    unit

  val boolean_model : t -> Satml_types.Atom.atom list
  val instantiation_context :
    t -> Satml_types.Flat_Formula.hcons_env -> Satml_types.Atom.Set.t
  val current_tbox : t -> th
  val set_current_tbox : t -> th -> unit
  val empty : unit -> t

  val assume_th_elt : t -> Expr.th_elt -> Explanation.t -> unit
  val decision_level : t -> int
  val cancel_until : t -> int -> unit

  val update_lazy_cnf :
    t ->
    do_bcp : bool ->
    Satml_types.Atom.atom option Flat_Formula.Map.t -> dec_lvl:int -> unit

  val exists_in_lazy_cnf : t -> Flat_Formula.t -> bool
  val known_lazy_formulas : t -> int Flat_Formula.Map.t

  val reason_of_deduction: Atom.atom -> Atom.Set.t
  val assume_simple : t -> Atom.atom list list -> unit

  val decide : t -> Atom.atom -> unit
  val conflict_analyze_and_fix : t -> conflict_origin -> unit

  val push : t -> Satml_types.Atom.atom -> unit
  val pop : t -> unit

end

module Make (Th : Theory.S) : SAT_ML with type th = Th.t

