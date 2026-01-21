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

type 'a literal = LTerm of Expr.t | LSem of 'a Xliteral.view

type instances = (Expr.t list * Expr.gformula * Explanation.t) list

type 'a input =
  'a Xliteral.view * Expr.t option * Explanation.t * Th_util.lit_origin

type 'a fact = 'a literal * Explanation.t * Th_util.lit_origin

type 'a facts = {
  equas     : 'a fact Queue.t;
  diseqs  : 'a fact Queue.t;
  ineqs   : 'a fact Queue.t;
  mutable touched : 'a Util.MI.t;
}

type 'a result = {
  assume : 'a fact list;
  remove: Expr.t list;
}

module type RELATION = sig
  type t

  val empty : Expr.Set.t list -> t

  val assume : t ->
    Uf.t -> (Shostak.Combine.r input) list -> t * Shostak.Combine.r result
  val query  : t -> Uf.t -> Shostak.Combine.r input -> Th_util.answer

  val case_split :
    t -> Uf.t ->
    for_model:bool ->
    (Shostak.Combine.r Xliteral.view * bool * Th_util.lit_origin) list
  (** case_split env returns a list of equalities *)

  val add : t -> Uf.t -> Shostak.Combine.r -> Expr.t ->
    t * (Shostak.Combine.r Xliteral.view * Explanation.t) list
  (** add a representant to take into account *)

  val instantiate :
    do_syntactic_matching:bool ->
    Matching_types.info Expr.Map.t * Expr.t list Expr.Map.t Symbols.Map.t ->
    t -> Uf.t -> (Expr.t -> Expr.t -> bool) ->
    t * instances

  val print_model :
    Format.formatter -> t -> (Expr.t * Shostak.Combine.r) list -> unit

  val new_terms : t -> Expr.Set.t

  val assume_th_elt : t -> Expr.th_elt -> Explanation.t -> t

end

