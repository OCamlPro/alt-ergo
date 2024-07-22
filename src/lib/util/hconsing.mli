(**************************************************************************)
(*                                                                        *)
(*     Alt-Ergo: The SMT Solver For Software Verification                 *)
(*     Copyright (C) --- OCamlPro SAS                                     *)
(*                                                                        *)
(*     This file is distributed under the terms of OCamlPro               *)
(*     Non-Commercial Purpose License, version 1.                         *)
(*                                                                        *)
(*     As an exception, Alt-Ergo Club members at the Gold level can       *)
(*     use this file under the terms of the Apache Software License       *)
(*     version 2.0.                                                       *)
(*                                                                        *)
(*     ---------------------------------------------------------------    *)
(*                                                                        *)
(*     The Alt-Ergo theorem prover                                        *)
(*                                                                        *)
(*     Sylvain Conchon, Evelyne Contejean, Francois Bobot                 *)
(*     Mohamed Iguernelala, Stephane Lescuyer, Alain Mebsout              *)
(*                                                                        *)
(*     CNRS - INRIA - Universite Paris Sud                                *)
(*                                                                        *)
(*     ---------------------------------------------------------------    *)
(*                                                                        *)
(*     More details can be found in the directory licenses/               *)
(*                                                                        *)
(**************************************************************************)


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

  val make : t -> t
  (** Hashcons a value [t], either returning [t], or a value equal
      to [t] that was hashconsed previously. *)

  val elements : unit -> t list
  (** Returns the list of all unique hashconsed elements. *)

end

module Make(H : HASHED) : (S with type t = H.elt)
(** Functor to create a hashconsing module from a module describing values. *)


