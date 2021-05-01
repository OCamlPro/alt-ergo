(**************************************************************************)
(*                                                                        *)
(*     Alt-Ergo: The SMT Solver For Software Verification                 *)
(*     Copyright (C) 2013-2023 --- OCamlPro SAS                           *)
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
(*     Until 2013, some parts of this code were released under            *)
(*     the Apache Software License version 2.0.                           *)
(*                                                                        *)
(*     ---------------------------------------------------------------    *)
(*                                                                        *)
(*     More details can be found in the directory licenses/               *)
(*                                                                        *)
(**************************************************************************)

type builtin =
    LE | LT (* arithmetic *)
  | IsConstr of Hstring.t (* ADT tester *)

type operator =
  | Tite
  (* Arithmetic *)
  | Plus | Minus | Mult | Div | Modulo | Pow
  | Reach
  (* ADTs *)
  | Access of Hstring.t | Record
  | Constr of Hstring.t (* enums, adts *)
  | Destruct of Hstring.t * bool
  (* Arrays *)
  | Get | Set
  (* BV *)
  | Concat
  | Extract of int * int (* lower bound * upper bound *)
  | BVnot | BVand | BVor | Int2BV of int | BV2Nat
  (* FP *)
  | Float
  | Integer_round | Fixed
  | Sqrt_real | Sqrt_real_default | Sqrt_real_excess
  | Abs_int | Abs_real | Real_of_int | Real_is_int
  | Int_floor | Int_ceil | Integer_log2
  | Max_real | Max_int | Min_real | Min_int
  | Not_theory_constant | Is_theory_constant | Linear_dependency
  | Optimize of {order : int; is_max : bool}

type lit =
  (* literals *)
  | L_eq
  | L_built of builtin
  | L_neg_eq
  | L_neg_built of builtin
  | L_neg_pred

type form =
  (* formulas *)
  | F_Unit of bool
  | F_Clause of bool
  | F_Iff
  | F_Xor
  | F_Lemma
  | F_Skolem

type name_kind = Ac | Other

type bound_kind = VarBnd of Var.t | ValBnd of Numbers.Q.t

type bound = private
  { kind : bound_kind; sort : Ty.t; is_open : bool; is_lower : bool }

type t =
  | True
  | False
  | Void
  | Name of Hstring.t * name_kind * bool
  | Int of Hstring.t
  | Real of Hstring.t
  | Bitv of string
  | Op of operator
  | Lit of lit
  | Form of form
  | Var of Var.t
  | In of bound * bound
  | MapsTo of Var.t
  | Let

val name : ?kind:name_kind -> ?defined:bool -> string -> t
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

module Set : Set.S with type elt = t

module Map : sig
  include Map.S with type key = t
  val print :
    (Format.formatter -> 'a -> unit) -> Format.formatter -> 'a t -> unit
end
