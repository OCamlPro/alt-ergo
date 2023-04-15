(******************************************************************************)
(*                                                                            *)
(*     The Alt-Ergo theorem prover                                            *)
(*     Copyright (C) 2006-2013                                                *)
(*                                                                            *)
(*     Sylvain Conchon                                                        *)
(*     Evelyne Contejean                                                      *)
(*                                                                            *)
(*     Francois Bobot                                                         *)
(*     Mohamed Iguernelala                                                    *)
(*     Stephane Lescuyer                                                      *)
(*     Alain Mebsout                                                          *)
(*                                                                            *)
(*     CNRS - INRIA - Universite Paris Sud                                    *)
(*                                                                            *)
(*     This file is distributed under the terms of the Apache Software        *)
(*     License version 2.0                                                    *)
(*                                                                            *)
(*  ------------------------------------------------------------------------  *)
(*                                                                            *)
(*     Alt-Ergo: The SMT Solver For Software Verification                     *)
(*     Copyright (C) 2013-2018 --- OCamlPro SAS                               *)
(*                                                                            *)
(*     This file is distributed under the terms of the Apache Software        *)
(*     License version 2.0                                                    *)
(*                                                                            *)
(******************************************************************************)

open Types

type t = Types.symbol

val name : ?kind:name_kind -> string -> t
val var : Var.t -> t
val underscore : t
val int : string -> t
val real : string -> t
val constr : string -> t
val destruct : guarded:bool -> string -> t
val mk_bound : bound_kind -> Ty.t -> is_open:bool -> is_lower:bool -> bound
val mk_in : bound -> bound -> t
val mk_maps_to : Var.t -> t

val is_ac : t -> bool

val equal : t -> t -> bool
val compare : t -> t -> int
val compare_bounds : bound -> bound -> int
val hash : t -> int

val to_string : t -> string
val print : Format.formatter -> t -> unit

val to_string_clean : t -> string
val print_clean : Format.formatter -> t -> unit

(*val dummy : t*)

val fresh : ?is_var:bool -> string -> t

val reinit_fresh_sy_cpt : unit -> unit
(** Resets to 0 the fresh symbol counter *)

val is_get : t -> bool
val is_set : t -> bool

val fake_eq  : t
val fake_neq : t
val fake_lt  : t
val fake_le  : t


val add_label : Hstring.t -> t -> unit
val label : t -> Hstring.t

val print_bound : Format.formatter -> bound -> unit
val string_of_bound : bound -> string

val clear_labels : unit -> unit
(** Empties the labels Hashtable *)

module Set = Types.SYMBOL.Set

module Map = Types.SYMBOL.Map

val print_map :
  (Format.formatter -> 'a -> unit) -> Format.formatter -> 'a Map.t -> unit
