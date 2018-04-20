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

exception Timeout

module MI : Map.S with type key = int
module SS : Set.S with type elt = string

(** Different values for -case-split-policy option:
 -after-theory-assume (default value): after assuming facts in theory by the SAT
 -before-matching: just before performing a matching round
 -after-matching: just after performing a matching round
 **)
type case_split_policy =
  | AfterTheoryAssume (* default *)
  | BeforeMatching
  | AfterMatching


type inst_kind = Normal | Forward | Backward

type sat_solver =
  | Tableaux
  | CDCL_satML


val set_status : string -> unit
val get_status : unit -> string

(*
(** This function is intended to be used with Map.merge in order to perform a
    union of two maps. The first argument is an equality function used to
    assert that bindings present in boths maps have the same value **)
val map_merge_is_union :
  ('a -> 'a -> bool) -> 'b ->
  ('a * int) option -> ('a * int) option -> ('a * int) option
*)
