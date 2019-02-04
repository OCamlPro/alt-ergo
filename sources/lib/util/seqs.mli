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

(** Sequence utilies

    This modules defines some helper functions on sequences.
*)

val flat_map_rec : ('a -> [ `Ok | `Seq of 'a Seq.t ]) -> 'a Seq.t -> 'a Seq.t
(** Recursive flat_map *)


