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

module Combine : Sig.X

module Polynome : Polynome.T
  with type r = Combine.r

module Arith : Sig.SHOSTAK
  with type r = Combine.r and type t = Polynome.t

module Records : Sig.SHOSTAK
  with type r = Combine.r and type t = Combine.r Records.abstract

module Bitv : Sig.SHOSTAK
  with type r = Combine.r and type t = Combine.r Bitv.abstract

module Arrays : Sig.SHOSTAK
  with type r = Combine.r and type t = Combine.r Arrays.abstract

module Enum : Sig.SHOSTAK
  with type r = Combine.r and type t = Combine.r Enum.abstract

module Adt : Sig.SHOSTAK
  with type r = Combine.r and type t = Combine.r Adt.abstract

module Ite : Sig.SHOSTAK
  with type r = Combine.r and type t = Combine.r Ite.abstract

module Ac : Ac.S with type r = Combine.r and type t = Combine.r Sig.ac

(** map of semantic values using Combine.hash_cmp *)
module MXH : Map.S with type key = Combine.r

(** set of semantic values using Combine.hash_cmp *)
module SXH : Set.S with type elt = Combine.r

(** map of semantic values using structural compare Combine.str_cmp *)
module MXS : Map.S with type key = Combine.r

(** set of semantic values using structural compare Combine.str_cmp *)
module SXS : Set.S with type elt = Combine.r
