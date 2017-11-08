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
(*     Copyright (C) 2013-2017 --- OCamlPro SAS                               *)
(*                                                                            *)
(*     This file is distributed under the terms of the Apache Software        *)
(*     License version 2.0                                                    *)
(*                                                                            *)
(******************************************************************************)

type operator =
  | Plus | Minus | Mult | Div | Modulo
  | Concat | Extract | Get | Set | Fixed | Float
  | Reach | Access of Hstring.t | Record
  | Sqrt_real | Abs_int | Abs_real | Real_of_int | Int_floor | Int_ceil
  | Sqrt_real_default | Sqrt_real_excess
  | Min_real | Min_int | Max_real | Max_int | Integer_log2 | Pow_real_int
  | Pow_real_real | Integer_round

type name_kind = Ac | Constructor | Other

type bound_kind = VarBnd of Hstring.t | ValBnd of Numbers.Q.t

type bound = private
  { kind : bound_kind; sort : Ty.t; is_open : bool; is_lower : bool }

type t =
  | True
  | False
  | Void
  | Name of Hstring.t * name_kind
  | Int of Hstring.t
  | Real of Hstring.t
  | Bitv of string
  | Op of operator
  | Var of Hstring.t
  | In of bound * bound
  | MapsTo of Hstring.t

val name : ?kind:name_kind -> string -> t
val var : string -> t
val underscoring : t -> t
val int : string -> t
val real : string -> t
val mk_bound : Hstring.t -> Ty.t -> is_open:bool -> is_lower:bool -> bound
val mk_in : bound -> bound -> t
val mk_maps_to : Hstring.t -> t

val is_ac : t -> bool

val equal : t -> t -> bool
val compare : t -> t -> int
val hash : t -> int

val to_string : t -> string
val print : Format.formatter -> t -> unit

val to_string_clean : t -> string
val print_clean : Format.formatter -> t -> unit

val dummy : t

val fresh : string -> t

val is_get : t -> bool
val is_set : t -> bool

val fake_eq  : t
val fake_neq : t
val fake_lt  : t
val fake_le  : t

module Map : Map.S with type key = t
module Set : Set.S with type elt = t

val add_label : Hstring.t -> t -> unit
val label : t -> Hstring.t

val print_bound : Format.formatter -> bound -> unit
