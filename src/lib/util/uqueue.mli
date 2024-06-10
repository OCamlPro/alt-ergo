(**************************************************************************)
(*                                                                        *)
(*     Alt-Ergo: The SMT Solver For Software Verification                 *)
(*     Copyright (C) 2022-2024 --- OCamlPro SAS                           *)
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
(*     More details can be found in the directory licenses/               *)
(*                                                                        *)
(**************************************************************************)

(** First-in first-out *unique* queues.

    This module implements queues (FIFOs) without duplicates, with in-place
    modifications. Implemented as a wrapper around the [Queue] and [Hashtbl] (to
    ensure uniqueness) modules from the stdlib. *)

module type S = sig
  type elt
  (** The type of elements in the unique queue. *)

  type t
  (** The type of unique queues with [elt] elements. *)

  val create : int -> t
  (** Create a new empty unique queue. The [int] parameter is passed to the
      backing [Hashtbl] used to ensure uniqueness. *)

  val push : t -> elt -> unit
  (** [push q x] adds [x] at the end of the queue [q]. Does nothing if [x] is
      already present in the queue. *)

  exception Empty
  (** Raised when [pop] or [peek] are applied to an empty queue. *)

  val pop : t -> elt
  (** [pop q] removes and returns the first element in queue [q], or raises
      [Empty] if the queue is empty.

      @raise Empty if the queue is empty. *)

  val peek : t -> elt
  (** [peek q] returns the first element in queue [q] without removing it, or
      raises [Empty] if the queue is empty.

      @raise Empty if the queue is empty. *)

  val is_empty : t -> bool
  (** Returns [true] if the queue is empty, [false] otherwise. *)

  val clear : t -> unit
  (** Discard all elements from the queue. *)
end

module Make(H : Hashtbl.HashedType) : S with type elt = H.t
