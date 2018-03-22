(******************************************************************************)
(*                                                                            *)
(*     Alt-Ergo: The SMT Solver For Software Verification                     *)
(*     Copyright (C) 2013-2017 --- OCamlPro SAS                               *)
(*                                                                            *)
(*     This file is distributed under the terms of the license indicated      *)
(*     in the file 'License.OCamlPro'. If 'License.OCamlPro' is not           *)
(*     present, please contact us to clarify licensing.                       *)
(*                                                                            *)
(******************************************************************************)

type t

val init : int -> t
val in_heap : t -> int -> bool
val decrease : (int -> int -> bool) -> t -> int -> unit
(*val increase : (int -> int -> bool) -> t -> int -> unit*)
val size : t -> int
val is_empty : t -> bool
val insert : (int -> int -> bool) -> t -> int -> unit
val grow_to_by_double: t -> int -> unit
(*val update : (int -> int -> bool) -> t -> int -> unit*)
val remove_min : (int -> int -> bool) -> t -> int
val filter : t -> (int -> bool) -> (int -> int -> bool) -> unit
