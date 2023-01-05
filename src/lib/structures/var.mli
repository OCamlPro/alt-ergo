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

(** {1 Types} *)

type t
(** Type of variable. *)

(** {1 Data structures} *)

module Map : Map.S with type key = t
(** Module of maps of variable keys using {!val:compare} as comparison
    funciton. *)

module Set : Set.S with type elt = t
(** Module of sets of variables using {!val:compare} as comparison function. *)

(** {1 Constructors} *)

val of_hstring : Hstring.t -> t
(** [of_hstring hstr] constructs a new variable whose the name is given by
    [hstr]. *)

val of_string  : string -> t
(** [of_string str] constructs a new variable whose the name is given by [str].
    The name is hconsed. *)

val hstring : t -> Hstring.t

(** {1 Comparison functions} *)

val compare : t -> t -> int
(** [compare v1 v2] compares the two variables [v1] and [v2]. *)

val equal : t -> t -> bool
(** [equal v1 v2] tests the equality of [v1] and [v2]. The function is
    equivalent to [compare v1 v2 = 0]. *)

val hash : t -> int
(** [hash v] computes the hash of the variable [v]. *)

val pp : Format.formatter -> t -> unit
(** [pp fmt v] pretty prints the variable [v] on the formatter [fmt]. *)

val show : t -> string
(** [show v] produces the string displayed by {!val pp}. *)

val save_cnt: unit -> unit
(** Saves the values of the counter. *)

val reinit_cnt: unit -> unit
(** Reinitializes the counter to the saved value with [save_cnt], 1 if no value
    is saved, since after the initialization of the modules [cnt] is set to 1
    when initializing the [underscore] constant in the Symbols module *)
