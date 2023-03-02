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

module MI : Map.S with type key = int
module SI : Set.S with type elt = int
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


type inst_mode = Normal | Forward | Backward

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

val show_axiom_kind : axiom_kind -> string
val th_ext_of_string : string -> theories_extensions option
val show_th_ext : theories_extensions -> string

(** Generic function for comparing algebraic data values. *)
val compare_algebraic : 'a -> 'a -> (('a * 'a) -> int) -> int

type matching_env = {
  nb_triggers : int;
  triggers_var : bool;
  no_ematching: bool;
  (** Flag to disable the e-matching. *)

  greedy : bool;
  use_cs : bool;

  inst_mode : inst_mode
  (** Mode of instantiation. *)
}

(** Loops from 0 to [max] and returns
    [(f max elt ... (f 1 elt (f 0 elt init)))...)].
    Returns [init] if [max] < 0. *)
val loop:
  f : (int -> 'a -> 'b -> 'b) ->
  max : int ->
  elt : 'a ->
  init : 'b ->
  'b

val print_list:
  sep:string ->
  pp:(Format.formatter -> 'a -> unit) ->
  Format.formatter -> 'a list -> unit

val print_list_pp:
  sep:(Format.formatter -> unit -> unit) ->
  pp:(Format.formatter -> 'a -> unit) ->
  Format.formatter -> 'a list -> unit
