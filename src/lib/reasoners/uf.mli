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

type t

type r = Shostak.Combine.r

module LX : Xliteral.S with type elt = r

val empty : unit -> t
val add : t -> Expr.t -> t * Expr.t list

val mem : t -> Expr.t -> bool

val find : t -> Expr.t -> r * Explanation.t

val find_r : t -> r -> r * Explanation.t

val union :
  t -> r -> r -> Explanation.t ->
  t * (r * (r * r * Explanation.t) list * r) list

val distinct : t -> r list -> Explanation.t -> t

val are_equal : t -> Expr.t -> Expr.t -> added_terms:bool -> Th_util.answer
val are_distinct : t -> Expr.t -> Expr.t -> Th_util.answer
val already_distinct : t -> r list -> bool

val class_of : t -> Expr.t -> Expr.t list
val rclass_of : t -> r -> Expr.Set.t

val cl_extract : t -> Expr.Set.t list
val model : t ->
  (r * Expr.t list * (Expr.t * r) list) list * (Expr.t list) list

val print : t -> unit
val term_repr : t -> Expr.t -> Expr.t

val make : t -> Expr.t -> r (* may raise Not_found *)

val is_normalized : t -> r -> bool

val assign_next : t -> (r Xliteral.view * bool * Th_util.lit_origin) list * t
val output_concrete_model : t -> unit
