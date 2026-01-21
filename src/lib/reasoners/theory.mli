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

module type S = sig
  type t

  val empty : unit -> t

  (* the first int is the decision level (dlvl) and the second one is the
     propagation level (plvl). The facts (first argument) are sorted in
     decreasing order with respect to (dlvl, plvl) *)
  val assume :
    ?ordered:bool ->
    (Expr.t * Explanation.t * int * int) list -> t ->
    t * Expr.Set.t * int

  val query : Expr.t -> t -> Th_util.answer
  val print_model : Format.formatter -> t -> unit
  val cl_extract : t -> Expr.Set.t list
  val extract_ground_terms : t -> Expr.Set.t
  val get_real_env : t -> Ccx.Main.t
  val get_case_split_env : t -> Ccx.Main.t
  val do_case_split : t -> t * Expr.Set.t
  val add_term : t -> Expr.t -> add_in_cs:bool -> t

  val compute_concrete_model : t -> t

  val assume_th_elt : t -> Expr.th_elt -> Explanation.t -> t
  val theories_instances :
    do_syntactic_matching:bool ->
    Matching_types.info Expr.Map.t * Expr.t list Expr.Map.t Symbols.Map.t ->
    t -> (Expr.t -> Expr.t -> bool) ->
    int -> int -> t * Sig_rel.instances

  val get_assumed : t -> Expr.Set.t
end

module Main_Default : S
module Main_Empty : S
