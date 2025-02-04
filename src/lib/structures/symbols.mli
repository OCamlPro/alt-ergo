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

type builtin =
    LE | LT (* arithmetic *)
  | IsConstr of Dolmen.Std.Expr.term_cst (* ADT tester *)
  | BVULE (* unsigned bit-vector arithmetic *)

type operator =
  | Tite
  (* Arithmetic *)
  | Plus | Minus | Mult | Div | Modulo | Pow
  (* ADTs *)
  | Access of Dolmen.Std.Expr.term_cst | Record
  | Constr of Dolmen.Std.Expr.term_cst (* enums, adts *)
  | Destruct of Dolmen.Std.Expr.term_cst
  (* Arrays *)
  | Get | Set
  (* BV *)
  | Concat
  | Extract of int * int (* lower bound * upper bound *)
  | Sign_extend of int
  | Repeat of int
  | BVnot | BVand | BVor | BVxor
  | BVadd | BVsub | BVmul | BVudiv | BVurem
  | BVshl | BVlshr
  | Int2BV of int | BV2Nat
  (* FP *)
  | Float
  | Integer_round
  | Sqrt_real | Sqrt_real_default | Sqrt_real_excess
  | Abs_int | Abs_real | Real_of_int | Real_is_int
  | Int_floor | Int_ceil | Integer_log2
  | Max_real | Max_int | Min_real | Min_int
  | Not_theory_constant | Is_theory_constant | Linear_dependency

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

type bound_kind = Unbounded | VarBnd of Var.t | ValBnd of Numbers.Q.t

type bound = private
  { kind : bound_kind; sort : Ty.t; is_open : bool; is_lower : bool }

type t =
  | True
  | False
  | Name of { id : Id.t ; kind : name_kind }
  | Int of Z.t
  | Real of Q.t
  | Bitv of int * Z.t
  | Op of operator
  | Lit of lit
  | Form of form
  | Var of Var.t
  | In of bound * bound
  | MapsTo of Var.t
  | Let

val name : ?kind:name_kind -> Id.t -> t
(** Create a new symbol with the given identifier.
    By default, the kind is is [Other]. *)

val var : Var.t -> t
val int : string -> t
val bitv : string -> t
val real : string -> t
val constr : Dolmen.Std.Expr.term_cst -> t
val destruct : Dolmen.Std.Expr.term_cst -> t
val mk_bound : bound_kind -> Ty.t -> is_open:bool -> is_lower:bool -> bound
val mk_in : bound -> bound -> t
val mk_maps_to : Var.t -> t

val is_ac : t -> bool

val is_internal : t -> bool
(** Check if the symbol is internal name that should never be printed on the
    regular output. *)

val equal : t -> t -> bool
val compare : t -> t -> int
val compare_bounds : bound -> bound -> int
val compare_operators : operator -> operator -> int
val hash : t -> int

val to_string : t -> string
val print : t Fmt.t
(* Printer used by debugging messages. *)

val to_string_clean : t -> string
val print_clean : t Fmt.t

val pp_ae_operator : operator Fmt.t
(** [pp_ae_operator ppf op] prints the operator symbol [op] on the
    formatter [ppf] using the Alt-Ergo native format. *)

val pp_smtlib_operator : operator Fmt.t
(** [pp_smtlib_operator ppf op] prints the operator symbol [op] on the
    formatter [ppf] using the SMT-LIB format. *)

(*val dummy : t*)

val fresh_skolem_var : string -> Var.t
val fresh_skolem_name : string -> t

(** Resets to 0 the fresh symbol counter *)

val is_get : t -> bool
val is_set : t -> bool

val add_label : Hstring.t -> t -> unit
val label : t -> Hstring.t

val print_bound : Format.formatter -> bound -> unit
val string_of_bound : bound -> string

val clear_labels : unit -> unit
(** Empties the labels Hashtable *)

module Set : Set.S with type elt = t

module Map : Map.S with type key = t
