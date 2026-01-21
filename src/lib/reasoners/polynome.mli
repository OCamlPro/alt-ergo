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

exception Not_a_num
exception Maybe_zero

module type S = sig
  include Sig.X
  val mult : r -> r -> r
end

module type T = sig

  type r
  type t

  val compare : t -> t -> int
  val equal : t -> t -> bool
  val hash : t -> int

  val create : (Numbers.Q.t * r) list -> Numbers.Q.t -> Ty.t-> t
  val add : t -> t -> t
  val sub : t -> t -> t
  val mult : t -> t -> t
  val mult_const : Numbers.Q.t -> t -> t
  val add_const : Numbers.Q.t -> t -> t
  val div : t -> t -> t * bool
  val modulo : t -> t -> t

  val is_const : t -> Numbers.Q.t option
  val is_empty : t -> bool
  val find : r -> t -> Numbers.Q.t
  val choose : t -> Numbers.Q.t * r
  val subst : r -> t -> t -> t
  val remove : r -> t -> t
  val to_list : t -> (Numbers.Q.t * r) list * Numbers.Q.t
  val leaves : t -> r list

  val print : Format.formatter -> t -> unit
  val type_info : t -> Ty.t
  val is_monomial : t -> (Numbers.Q.t * r * Numbers.Q.t) option

  (* PPMC des denominateurs des coefficients excepte la constante *)
  val ppmc_denominators : t -> Numbers.Q.t
  (* PGCD des numerateurs des coefficients excepte la constante *)
  val pgcd_numerators : t -> Numbers.Q.t
  (* retourne un polynome sans constante et sa constante
     et la constante multiplicative:
     normal_form p = (p',c,d) <=> p = (p' + c) * d *)
  val normal_form : t -> t * Numbers.Q.t * Numbers.Q.t
  (* comme normal_form mais le signe est aussi normalise *)
  val normal_form_pos : t -> t * Numbers.Q.t * Numbers.Q.t

  val abstract_selectors : t -> (r * r) list -> t * (r * r) list

  val separate_constant : t -> t * Numbers.Q.t
end

module type EXTENDED_Polynome = sig
  include T
  val extract : r -> t option
  val embed : t -> r
end

module Make (X : S) : T with type r = X.r

