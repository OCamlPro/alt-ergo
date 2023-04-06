(******************************************************************************)
(*                                                                            *)
(*     The Alt-Ergo theorem prover                                            *)
(*     Copyright (C) 2006-2013                                                *)
(*                                                                            *)
(*     Sylvain Conchon                                                        *)
(*     Evelyne Contejean                                                      *)
(*                                                                            *)
(*     Francois Bobot                                                         *)
(*     Mohamed Iguernelala                                                    *)
(*     Stephane Lescuyer                                                      *)
(*     Alain Mebsout                                                          *)
(*                                                                            *)
(*     CNRS - INRIA - Universite Paris Sud                                    *)
(*                                                                            *)
(*     This file is distributed under the terms of the Apache Software        *)
(*     License version 2.0                                                    *)
(*                                                                            *)
(*  ------------------------------------------------------------------------  *)
(*                                                                            *)
(*     Alt-Ergo: The SMT Solver For Software Verification                     *)
(*     Copyright (C) 2013-2018 --- OCamlPro SAS                               *)
(*                                                                            *)
(*     This file is distributed under the terms of the Apache Software        *)
(*     License version 2.0                                                    *)
(*                                                                            *)
(******************************************************************************)


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

  val save_cache: unit -> unit
  (** Saves the module's cache *)

  val reinit_cache: unit -> unit
  (** Reinitializes the module's cache *)

  val enable_gc_control : unit -> unit
  (** Set whether the GC control should be activated.
   *
   *  GC control allows to ensure that hashconsed values are only collected at
   *  specific points that is controlled by the Hconsing module rather than
   *  depend on the behavior of the OCaml GC.
   *
   *  Must be set only once before the first call to `make`.
   *)

  val make : t -> t
  (** Hashcons a value [t], either returning [t], or a value equal
      to [t] that was hashconsed previously. *)

  val elements : unit -> t list
  (** Returns the list of all unique hashconsed elements. *)

end

module Make(H : HASHED) : (S with type t = H.elt)
(** Functor to create a hashconsing module from a module describing values. *)


