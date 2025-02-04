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

type t
(** Type of variable. *)

val of_id : Id.t -> t
(** Create a variable from an identifier. *)

val local : Id.t -> t
(** Create a new "local" variable. Local variables are variables used
    exclusively in user-defined theories for semantic triggers, and are
    implicitly bound at the level of the enclosing quantifier.
    They must starts with `?`. *)

val underscore : t
(** Unique special variable. Used to indicate fields that should be ignored in
    pattern matching and triggers. *)

val is_local : t -> bool
(** Indicates whether the given variable is a local variable (see {!local} above
    for details). *)

val compare : t -> t -> int

val equal : t -> t -> bool

val hash : t -> int

val uid : t -> int
(** Globally unique identifier for the variable. *)

val pp : Format.formatter -> t -> unit

val show : t -> string

module Set : Set.S with type elt = t

module Map : sig
  include Map.S with type key = t
  val pp : 'a Fmt.t -> 'a t Fmt.t
end
