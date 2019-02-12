(******************************************************************************)
(*                                                                            *)
(*     Alt-Ergo: The SMT Solver For Software Verification                     *)
(*     Copyright (C) 2013-2018 --- OCamlPro SAS                               *)
(*                                                                            *)
(*     This file is distributed under the terms of the license indicated      *)
(*     in the file 'License.OCamlPro'. If 'License.OCamlPro' is not           *)
(*     present, please contact us to clarify licensing.                       *)
(*                                                                            *)
(******************************************************************************)

(** Integer heaps

    This modules define priority heaps over integers.
*)

(** {2 Integer heaps} *)

type t
(** The type of heaps. *)

val init : int -> t
(** Create a heap with the given initial size. *)

val in_heap : t -> int -> bool
(** Heap membership function. *)

val decrease : (int -> int -> bool) -> t -> int -> unit
(** Decrease activity of the given integer.
    TODO: document the comparison function ! *)

val increase : (int -> int -> bool) -> t -> int -> unit
(** Increase activity of the given integer.
    TODO: document the comparison function ! *)

val size : t -> int
(** Returns the current size of the heap. *)

val is_empty : t -> bool
(** Is the heap empty ? *)

val insert : (int -> int -> bool) -> t -> int -> unit
(** Inset a new element in the heap.
    TODO: document comparison function. *)

val grow_to_by_double: t -> int -> unit
(** Grow the size of the heap by multiplying it by 2
    until it is at least the size specified. *)

val remove_min : (int -> int -> bool) -> t -> int
(** Remove the minimum element from the heap and return it. *)

val filter : t -> (int -> bool) -> (int -> int -> bool) -> unit
(** Filter elements in the heap.
    TODO: document comparison function ! *)

