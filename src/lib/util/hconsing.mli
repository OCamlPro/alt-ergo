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


(** Generic Hashconsing.

    This module defines generic hashconsing over structures.
*)

(** {2 Hashconsing} *)

module type HASHED = sig

  (** Hashed values.

      This signature defines the interface required for
      values to be hashconsed. *)

  type elt
  (** The type of hashed elements*)

  val eq : elt -> elt -> bool
  (** Equality predicate on values. *)

  val hash : elt -> int
  (** Hash function on values. Must be compatible with the equality
      function, i.e: equality of values imply that hashes are equal. *)

  val set_id : int -> elt -> elt
  (** Set an id to the given value.
      This id should not be considered by the equality function
      when comparing values.
      Should not mutate the given value for the hashconsing to be correct. *)

  val initial_size : int
  (** Initial size for the hashconsing table. *)

  val disable_weaks : unit -> bool
  (** Values hashconsed when this returns [true] are treated
      as always reachable by the gc and thus will not be collected. *)

end

module type S = sig

  (** Hashconsed values

      This signature defines a hashconsing module,
      used to implement maximal sharing of hashconsed values. *)

  type t
  (** The type of value used. *)

  val make : t -> t
  (** Hashcons a value [t], either returning [t], or a value equal
      to [t] that was hashconsed previously. *)

  val elements : unit -> t list
  (** Returns the list of all unique hashconsed elements. *)

end

module Make(H : HASHED) : (S with type t = H.elt)
(** Functor to create a hashconsing module from a module describing values. *)


