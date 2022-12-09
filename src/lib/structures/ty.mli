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

(** Types

    This module defines the witness of types. *)

(** {2 Definition} *)

type t =
  | Tint
  (** Integer numbers. *)

  | Treal
  (** Real numbers. *)

  | Tbool
  (** Booleans. *)

  | Tunit
  (** The unit type. *)

  | Tvar of tvar
  (** Type variables. *)

  | Tbitv of int
  (** Bitvectors of a given length. *)

  | Trecord of trecord
  (** Record type. *)

  | Text of {
      constr : Hstring.t;
      args : t list
    }
  (** Abstract types applied to arguments. [Text {constr; args}] is the
      application of the abstract type constructor [constr] to arguments
      [args]. *)

  | Tfarray of {
      key_ty : t;
      val_ty : t;
    }
  (** Functional arrays. [TFarray {key_ty; val_ty}] maps values of type
      [key_ty] to values of type [val_ty]. *)

  | Tsum of {
      name : Hstring.t;
      constrs : Hstring.t list
    }
  (** Enumeration, with its name, and the list of its constructors. *)

  | Tadt of {
      constr : Hstring.t;
      args : t list
    }
  (** Algebraic types applied to arguments. [Tadt {constr; args}] is the
      application of the datatype constructor [constr] to arguments [args]. *)
(** Type of witness. *)

and tvar = {
  v : int;
  (** Unique identifier. *)

  mutable value : t option;
  (** Pointer to the current value of the type variable. *)
}
(** Type variables.
    The [value] field is mutated during unification,
    hence distinct types should have disjoints sets of
    type variables (see function {!val:fresh}). *)

and trecord = {
  mutable args : t list;
  (** Arguments passed to the record constructor *)

  name : Hstring.t;
  (** Name of the record type *)

  mutable lbs : (Hstring.t * t) list;
  (** List of fields of the record. Each field has a name,
      and an associated type. *)

  record_constr : Hstring.t;
  (** record constructor. Useful is case it's a specialization of an
      algeberaic datatype. Default value is "\{__[name]" *)
}
(** Record types. *)

type adt_constr = {
  constr : Hstring.t;
  (** Constructor of an ADT type. *)

  destrs : (Hstring.t * t) list
  (** the list of destructors associated with the constructor and their
      respective types *)
}

(** bodies of types definitions. Currently, bodies are inlined in the
    type [t] for records and enumerations. But, this is not possible
    for recursive ADTs *)
type type_body =
  | Adt of adt_constr list
  (** body of an algebraic datatype *)

(** {1 Data structures} *)

(** Sets of type variables, indexed by their identifier. *)
module Svty : Set.S with type elt = int

(** Sets of types *)
module Set : Set.S with type elt = t

val assoc_destrs : Hstring.t -> adt_constr list -> (Hstring.t * t) list
(** returns the list of destructors associated with the given consturctor.
    raises Not_found if the constructor is not in the given list *)

val type_body : Hstring.t -> t list -> type_body

(** {2 Type inspection} *)

val hash : t -> int
(** Hash function *)

val equal : t -> t -> bool
(** Equality function *)

val compare : t -> t -> int
(** Comparison function *)

val print : t Util.printer
(** Printing function for types (does not print
    the type of each fields for records). *)

val print_list : t list Util.printer
(** Print function for lists of types (does not print
    the type of each fields for records). *)

val print_full : t Util.printer
(** Print function including the record fields. *)

val vty_of : t -> Svty.t
(** Returns the set of type variables that occur in a given type. *)

(** {2 Constructors} *)

val tunit : t
(** The unit type. *)

val fresh_var : unit -> tvar
(** Generate a fresh type variable, guaranteed to be distinct
    from any other previously generated by this function. *)

val fresh_tvar : unit -> t
(** Wrap the {!val:fresh_var} function to return a type. *)

val fresh_empty_text : unit -> t
(** Return a fesh abstract type. *)

val text : args:t list -> string -> t
(** Apply the abstract type constructor to the list of type arguments given. *)

val tsum : constrs:string list -> string -> t
(** [tsum ~constrs name] creates an enumeration type named [name] with
    constructors [constrs]. *)

val t_adt :
  ?body:((string * (string * t) list) list) option ->
  args:t list ->
  string ->
  t
(** Create an algebraic datatype. The body is a list of constructors, where
    each constructor is associated with the list of its destructors with their
    respective types. If [body] is none, then no definition will be registered
    for this type. The second argument is the name of the type. The third one
    provides its list of arguments. *)

val trecord :
  ?record_constr:string ->
  args:t list ->
  fields:(string * t) list ->
  string ->
  t
(** Create a record type. [trecord args name lbs] creates a record
    type with name [name], arguments [args] and fields [lbs]. *)

(** {2 Substitutions} *)

(** The type of substitution, i.e. maps
    from type variables identifiers to types.*)
module Subst: sig
  type ty = t
  type t

  val empty : t
  val is_empty : t -> bool
  val add : int -> ty -> t -> t
  val remove : int -> t -> t
  val mem : int -> t -> bool
  val filter : (int -> ty -> bool) -> t -> t

  val apply : t -> ty -> ty
  (** Substitution application. *)

  val union : t -> t -> t
  (** [union u v] applies [v] to [u], resulting in [u'].
      It then computes the union of [u'] and [v], prioritizing
      bindings from [u'] in case of conflict. *)

  val compare : t -> t -> int
  (** Comparison of substitutions. *)

  val equal : t -> t -> bool
  (** Equality of substitutions. *)

  val print : t Util.printer
  (** Print function for substitutions. *)
end

(** {2 Unification/Matching} *)

exception TypeClash of t * t
(** Exception raised during matching or unification.
    [TypeClash (u, v)] is raised when [u] and [v] could not be
    matched or unified ([u] and [v] may be sub-types of the
    types being actually unified or matched). *)

val unify : t -> t -> unit
(** Destructive unification. Mutates the [value] fields of
    type variables.
    @raise TypeClash when unification is impossible. In this
      case, the [value] fields of already mutated type variables
      are left modified, which may prevent future unifications. *)

val matching : Subst.t -> t -> t -> Subst.t
(** Matching of types (non-destructive). [matching pat t] returns a
    substitution [subst] such that [apply_subst subst pat] is
    equal to [t]. *)

val shorten : t -> t
(** Shorten paths in type variables values.
    Unification in particular can create chains where the [value]
    field of one type variable points to another and so on...
    This function short-circuits such chains so that the value
    of a type variable can be accessed directly. *)

(** {2 Manipulations on types} *)

val fresh : t -> Subst.t -> t * Subst.t
(** Apply the given substitution, all while generating fresh variables
    for the variables not already bound in the substitution. Returns
    a substitution containing bindings from old variable to their
    fresh counterpart. *)

val fresh_list : t list -> Subst.t -> t list * Subst.t
(** Same as {!val:fresh} but on lists of types. *)

val instantiate : t list -> t list -> t -> t
(** [instantiate vars args t] builds the substitutions mapping
    each type variable in [vars] to the corresponding term in [args],
    then apply that substitution to [t].
    @raise Invalid_argument if the lists [vars] and [args]
      do not have the same length
    @raise Assertion_failure if one type in [vars] is not
      a type variable. *)

val monomorphize: t -> t
(** Return a monomorphized variant of the given type, where
    type variable without values have been replaced by abstract types. *)

val reinit_decls : unit -> unit
(** Empties the decls cache *)
