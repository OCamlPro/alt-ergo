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

exception Timeout

exception Step_limit_reached of int

exception Unsolvable

exception Cmp of int

exception Not_implemented of string

module MI : Map.S with type key = int

module SI : Set.S with type elt = int

module MS : Map.S with type key = string

module SS : Set.S with type elt = string

(** Different values for -case-split-policy option: -after-theory-assume
    (default value): after assuming facts in theory by the SAT -before-matching:
    just before performing a matching round -after-matching: just after
    performing a matching round **)
type case_split_policy =
  | AfterTheoryAssume (* default *)
  | BeforeMatching
  | AfterMatching

type inst_kind =
  | Normal
  | Forward
  | Backward

type sat_solver =
  | Tableaux
  | CDCL
  | CDCL_Tableaux

val pp_sat_solver : Format.formatter -> sat_solver -> unit

type theories_extensions =
  | Adt
  | Arrays
  | Bitv
  | LIA
  | LRA
  | NRA
  | NIA
  | FPA
  | RIA

type axiom_kind =
  | Default
  | Propagator

(** The different modes alt-ergo can be in.
    https://smtlib.cs.uiowa.edu/papers/smt-lib-reference-v2.6-r2017-07-18.pdf#52
*)
type mode =
  | Start
  | Assert
  | Sat
  | Unsat

val equal_mode : mode -> mode -> bool

val pp_mode : Format.formatter -> mode -> unit

val th_ext_of_string : string -> theories_extensions option

val string_of_th_ext : theories_extensions -> string

val compare_algebraic : 'a -> 'a -> ('a * 'a -> int) -> int
(** generic function for comparing algebraic data types.
    [compare_algebraic a b f]
    - Stdlib.compare a b is used if *)

val cmp_lists : 'a list -> 'a list -> ('a -> 'a -> int) -> int

type matching_env =
  { no_ematching : bool;
    use_cs : bool;
    backward : inst_kind
  }

type triggers_env =
  { nb_triggers : int;  (** Limit the number of trigger generated per axiom. *)
    triggers_var : bool;
        (** If [true], we allow trigger variables during the trigger generation.
        *)
    greedy : bool
  }

val loop : f:(int -> 'a -> 'b -> 'b) -> max:int -> elt:'a -> init:'b -> 'b
(** Loops from 0 to [max] and returns
    [(f max elt ... (f 1 elt (f 0 elt init)))...)]. Returns [init] if [max] < 0
*)

val print_list :
  sep:string ->
  pp:(Format.formatter -> 'a -> unit) ->
  Format.formatter ->
  'a list ->
  unit

val print_list_pp :
  sep:(Format.formatter -> unit -> unit) ->
  pp:(Format.formatter -> 'a -> unit) ->
  Format.formatter ->
  'a list ->
  unit

val internal_error : ('a, Format.formatter, unit, 'b) format4 -> 'a

module Syntax : sig
  val ( let& ) : (scope:('a -> 'b) -> 'b) -> ('a -> 'b) -> 'b
  (** [let&] is a "resource binding" operator from memprof-limits

      It provides a nice notation for resources cleaned up at the end of scope:

      {[
        let f x =
          let& () = Steps.with_step_limit limit in
          ...
      ]} *)
end

module Extra_options : sig
  (** This module allows to define new [-X] options.

      [-X] options can be passed on the command line as [-X name=value].

      {b Note}: [-X] options are intended for internal use only. They are not
      documented in the output of [--help] and may be removed without notice. *)

  val string : string -> string -> string -> unit -> string
  (** [string __LOC__ name default] defines a new extra option which accepts
      arbitrary strings. *)

  val int : string -> string -> int -> unit -> int
  (** [int __LOC__ name default] defines a new extra option which accepts only
      integers. *)

  val bool : string -> string -> unit -> bool
  (** [bool __LOC__ name] defines a new extra option which accepts booleans
      written as the integers '0' and '1'. In addition, [-X name] is equivalent
      to [-X name=1].

      Boolean options define a pair of options: [name] and [no-name], which are
      inverses of each others. *)

  val symbol : string -> string -> 'a -> (string * 'a) list -> unit -> 'a
  (** [symbol __LOC__ name default spec] defines a new extra option which
      accepts only the strings in [spec] and associates them with the
      corresponding value. *)

  val parse_and_set : string -> (unit, string) result
end
