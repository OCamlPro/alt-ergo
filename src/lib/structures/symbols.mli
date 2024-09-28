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
  | IsConstr of Uid.term_cst (* ADT tester *)
  | BVULE (* unsigned bit-vector arithmetic *)

type operator =
  | Tite
  (* Arithmetic *)
  | Plus | Minus | Mult | Div | Modulo | Pow
  (* ADTs *)
  | Access of Uid.term_cst | Record
  | Constr of Uid.term_cst (* enums, adts *)
  | Destruct of Uid.term_cst
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

(** The [name_space] type discriminates the different types of names. The same
    string in different name spaces is considered as different names.

    Note that the names stored in the [Name] constructor below are mangled
    during creation of the symbol: a special prefix is added depending on the
    name space. *)
type name_space =
  | User
  (** This symbol was defined by the user, and appears as is somewhere in a
      source file.

      As an exception, if the name we got from the user starts with either "."
      or "@" (which are prefixes reserved for solver use in the SMT-LIB
      standard), the name will be printed with an extra ".". So if the user
      writes ".x" or "@x", it will be printed as "..x" and ".@x" instead.

      Normally, this shouldn't occur, but we do this to ensure no confusion
      even if invalid names ever sneak through. *)
  | Internal
  (** This symbol is an internal implementation detail of the solver, such as
      a proxy formula or the abstracted counterpart of AC symbols.

      Internal names are printed with a ".!" prefix. *)
  | Fresh
  (** This symbol is a "fresh" internal name. Fresh internal names play a
      similar role as internal names, but they always represent a constant
      that was introduced during solving as part of some kind of purification
      or abstraction procedure.

      In order to correctly implement AC(X) in the presence of distributive
      symbols, symbols generated for AC(X) abstraction use a special
      namespace, [Fresh_ac] below.

      To ensure uniqueness, fresh names must always be generated using
      [Id.Namespace.Internal.fresh ()].

      In particular, fresh names are only used to denote constants, not
      arbitrary functions. *)
  | Fresh_ac
  (** This symbol has been introduced as part of the AC(X) abstraction process.
      This is notably used by some parts of AC(X) that check if terms contains
      fresh symbols (see [contains_a_fresh_alien] in the [Arith] module for an
      example).

      These correspond to the K sort in the AC(X) paper. They use a different
      name space from other fresh symbols because we need to be able to know
      whether a fresh symbol comes from the AC(X) abstraction procedure in order
      to prevent loops.

      To ensure uniqueness, AC abstraction names must always be generated using
      [Id.Namespace.Internal.fresh ()]. *)
  | Skolem
  (** This symbol has been introduced as part of skolemization, and represents
      the (dependent) variable of an existential quantifier. Skolem names can
      have arbitrary arity to depend on previous skolem names in binding order
      (so if you have `(exists (x y) e)` then there will be a skolem variable
      `sko_x` and a skolem function `(sko_y sko_x)`). *)
  | Abstract
  (** This symbol has been introduced as part of model generation, and
      represents an abstract value.

      To ensure uniqueness, abstract names must always be generated using
      [Id.Namespace.Abstract.fresh ()]. *)

type bound_kind = Unbounded | VarBnd of Var.t | ValBnd of Numbers.Q.t

type bound = private
  { kind : bound_kind; sort : Ty.t; is_open : bool; is_lower : bool }

type t =
  | True
  | False
  | Name of
      { hs : Uid.term_cst
      (** Note: [hs] is prefixed according to [ns]. *)
      ; kind : name_kind
      ; defined : bool
      ; ns : name_space }
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

module Namespace : sig
  module type S = sig
    val fresh : ?base:string -> unit -> string
  end

  module Internal : S
  module Skolem : S
  module Abstract : S

  val reinit : unit -> unit
  (** Resets the [fresh_internal_name], [fresh_skolem] and [fresh_abstract]
      counters. *)
end

(** Create a new symbol with the given name.

    By default, names are created in the [User] name space.

    Note that names are pre-mangled: the [hs] field of the resulting name may
    not be exactly the name that was passed to this function (however, calling
    `name` with the same string but two different name spaces is guaranteed to
    return two [Name]s with distinct [hs] fields). *)
val name :
  ?kind:name_kind -> ?defined:bool -> ?ns:name_space -> Uid.term_cst -> t

val var : Var.t -> t
val int : string -> t
val bitv : string -> t
val real : string -> t
val constr : Uid.term_cst -> t
val destruct : Uid.term_cst -> t
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
(* [pp_ae_operator ppf op] prints the operator symbol [op] on the
   formatter [ppf] using the Alt-Ergo native format. *)

val pp_smtlib_operator : operator Fmt.t
(* [pp_smtlib_operator ppf op] prints the operator symbol [op] on the
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
