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

type 'a t = { mutable dummy: 'a; mutable data : 'a array; mutable sz : int }
val make : int -> 'a -> 'a t
val init : int -> (int -> 'a) -> 'a -> 'a t
val from_array : 'a array -> int -> 'a -> 'a t
val from_list : 'a list -> int -> 'a -> 'a t
val clear : 'a t -> unit

(* if bool is true, then put "dummy" is unreachable cells *)
val shrink : 'a t -> int -> bool -> unit
val pop : 'a t -> unit
val size : 'a t -> int
val is_empty : 'a t -> bool
val grow_to : 'a t -> int -> unit
val grow_to_double_size : 'a t -> unit
val grow_to_by_double : 'a t -> int -> unit
val is_full : 'a t -> bool
val push : 'a t -> 'a -> unit
val push_none : 'a t -> unit
val last : 'a t -> 'a
val get : 'a t -> int -> 'a
val set : 'a t -> int -> 'a -> unit
val set_size : 'a t -> int -> unit
val copy : 'a t -> 'a t
val move_to : 'a t -> 'a t -> unit
val remove : 'a t -> 'a -> unit
val fast_remove : 'a t -> 'a -> unit
val sort : 'a t -> ('a -> 'a -> int) -> unit
val iter : 'a t -> ('a -> unit) -> unit
