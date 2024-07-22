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

val of_hstring : Hstring.t -> t
(** Create a *fresh* variable with the given name.

    Calling [of_hstring] twice with the same [Hstring.t] as argument will result
    in *distinct* variables. *)

val of_string  : string -> t
(** Convenient alias for [of_hstring (Hstring.make s)]. *)

val local : string -> t
(** Create a new "local" variable. Local variables are variables used
    exclusively in user-defined theories for semantic triggers, and are
    implicitly bound at the level of the enclosing quantifier. *)

val is_local : t -> bool
(** Indicates whether the given variable is a local variable (see {!local} above
    for details). *)

val compare : t -> t -> int

val equal : t -> t -> bool

val hash : t -> int

val uid : t -> int
(** Globally unique identifier for the variable. *)

val underscore : t
(** Unique special variable. Used to indicate fields that should be ignored in
    pattern matching and triggers. *)

val print : Format.formatter -> t -> unit

val to_string : t -> string

val save_cnt: unit -> unit
(** Saves the values of the counter  *)

val reinit_cnt: unit -> unit
(** Reinitializes the counter to the saved value with [save_cnt], 1 if no value
    is saved, since after the initialization of the modules [cnt] is set to 1
    when initializing the [underscore] constant in the Symbols module *)

module Set : Set.S with type elt = t

module Map : sig
  include Map.S with type key = t
  val pp : 'a Fmt.t -> 'a t Fmt.t
end
