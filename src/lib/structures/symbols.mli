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

(** {1 Types} *)

type builtin =
  (* Arithmetic *)
  | LE                    (** {b L}ess or {b e}qual symbol. *)
  | LT                    (** {b L}ess {b t}han symbol. *)
  (* ADT *)
  | IsConstr of Hstring.t (** ADT tester symbol. *)
(** Built-in symbols. *)

type operator =
  | Plus | Minus | Mult | Div | Modulo
  | Concat | Extract | Get | Set | Fixed | Float
  | Reach | Access of Hstring.t | Record
  | Sqrt_real | Abs_int | Abs_real | Real_of_int | Int_floor | Int_ceil
  | Sqrt_real_default | Sqrt_real_excess
  | Min_real | Min_int | Max_real | Max_int | Integer_log2
  | Pow | Integer_round
  | Cstr of Hstring.t (* enums, adts *)
  | Dstr of Hstring.t * bool
  | Tite
  (** Type of symbol of operator. *)

type lit =
  | L_eq
  | L_built of builtin
  | L_neg_eq
  | L_neg_built of builtin
  | L_neg_pred
  (** Type of symbol of literal. *)

type form =
  | F_Unit of bool
  | F_Clause of bool
  | F_Iff             (** Symbol of equivalence. *)
  | F_Xor             (** Symbol of exclusive disjunction. *)
  | F_Lemma
  | F_Skolem
  (** Type of symbol of formula. *)

type name_kind = Ac | Other

(** Specify if a bound is a variable or a literal number. *)
type bound_kind = VarBnd of Var.t | ValBnd of Numbers.Q.t

type bound = private {
  kind: bound_kind; (** Kind of the bound. *)
  sort: Ty.t;       (** Type of the bound.
                        It can be {!constructor:Ty.Tint} or
                        {!constructor:Ty.Treal}. *)
  is_open: bool;
  is_lower: bool
}
(** Type of symbol of bound. *)

(** Type of symbols. *)
type t =
  | True                           (** Top symbol. *)
  | False                          (** Bottom symbol. *)
  | Void                           (** Unit symbol. *)
  | Name of Hstring.t * name_kind
  | Int of Hstring.t
  | Real of Hstring.t
  | Bitv of string
  | Op of operator                 (** Operator symbol. *)
  | Lit of lit                     (** Literal symbol. *)
  | Form of form                   (** Formula symbol. *)
  | Var of Var.t                   (** Variable symbol. *)
  | In of bound * bound
  | MapsTo of Var.t
  | Let

(** {1 Data structures} *)

module Set : Set.S with type elt = t

module Map : sig
  include Map.S with type key = t
  val print :
    (Format.formatter -> 'a -> unit) -> Format.formatter -> 'a t -> unit
end

(** {1 Constructor} *)

val name: ?kind:name_kind -> string -> t

val var: Var.t -> t
(** [var v] converts a variable to symbol. *)

val underscore : t

val int: string -> t
(** [int str] produces the symbol of an integer literal. *)

val real: string -> t
(** [real str] produces the symbol of a real literal. *)

val cstr: string -> t
val dstr: guarded:bool -> string -> t
val mk_bound: bound_kind -> Ty.t -> is_open:bool -> is_lower:bool -> bound
val mk_in: bound -> bound -> t
val mk_maps_to: Var.t -> t

(** {1 Comparaison and test functions} *)

val equal : t -> t -> bool
val compare : t -> t -> int
val compare_bounds : bound -> bound -> int

val hash: t -> int

val is_ac : t -> bool
val is_get : t -> bool
val is_set : t -> bool
val is_ite : t -> bool

val is_infix : t -> bool
(** [is_infix sy] is [true] if and only if the symbol [sy] is an operator
    in infix position. *)

val is_prefix : t -> bool
(** [is_prefix sy] is [true] if and only if the symbol [sy] is an operator
    in prefix position. *)

(** {1 Printing} *)

val to_string : t -> string
(** [to_string sy] produces a string representing the symbol [sy]. *)

val print : Format.formatter -> t -> unit
(** [print fmt sy] pretty prints the symbol [sy] on the formatter [fmt]. *)

val to_string_clean: t -> string
val print_clean: Format.formatter -> t -> unit
val print_bound: Format.formatter -> bound -> unit
val string_of_bound: bound -> string

(*val dummy : t*)

val fresh: ?is_var:bool -> string -> t
(** [fresh str] produces a fresh name of the form [!?__str] where . *)

val reinit_fresh_sy_cpt: unit -> unit
(** Reset to zero the fresh symbol counter. *)

val fake_eq: t
val fake_neq: t
val fake_lt: t
val fake_le: t


val add_label: Hstring.t -> t -> unit
val label: t -> Hstring.t

val clear_labels: unit -> unit
(** Empties the labels Hashtable *)
