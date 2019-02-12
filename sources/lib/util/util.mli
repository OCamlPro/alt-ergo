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

exception Timeout
exception Unsolvable

exception Cmp of int

module MI : Map.S with type key = int
module SS : Set.S with type elt = string

(** Different values for -case-split-policy option:
    -after-theory-assume (default value): after assuming facts in
    theory by the SAT
    -before-matching: just before performing a matching round
    -after-matching: just after performing a matching round **)
type case_split_policy =
  | AfterTheoryAssume (* default *)
  | BeforeMatching
  | AfterMatching


type inst_kind = Normal | Forward | Backward

type sat_solver =
  | Tableaux
  | Tableaux_CDCL
  | CDCL
  | CDCL_Tableaux

type theories_extensions =
  | Sum
  | Adt
  | Arrays
  | Records
  | Bitv
  | LIA
  | LRA
  | NRA
  | NIA
  | FPA

type axiom_kind = Default | Propagator

val th_ext_of_string : string -> theories_extensions option
val string_of_th_ext : theories_extensions -> string

(**
   generic function for comparing algebraic data types.
   [compare_algebraic a b f]
   - Pervasives.compare a b is used if

*)
val [@inline always] compare_algebraic : 'a -> 'a -> (('a * 'a) -> int) -> int

val [@inline always] cmp_lists: 'a list -> 'a list -> ('a -> 'a -> int) -> int

type matching_env =
  {
    nb_triggers : int;
    triggers_var : bool;
    no_ematching: bool;
    greedy : bool;
    use_cs : bool;
    backward : inst_kind
  }

val print_list:
  sep:string ->
  pp:(Format.formatter -> 'a -> unit) ->
  Format.formatter -> 'a list -> unit

val print_list_pp:
  sep:(Format.formatter -> unit -> unit) ->
  pp:(Format.formatter -> 'a -> unit) ->
  Format.formatter -> 'a list -> unit
