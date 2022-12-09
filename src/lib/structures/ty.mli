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

(** Type of witness. *)
type t =
  | Tint                        (** Integer numbers. *)
  | Treal                       (** Real numbers. *)
  | Tbool                       (** Booleans. *)
  | Tunit                       (** The unit type. *)
  | Tvar of tvar                (** Type variables. *)
  | Tbitv of int                (** Bitvectors of a given length. *)
  | Trecord of trecord          (** Record type. *)

  | Text of {
      constr: Hstring.t;
      args: t list
    }
  (** Abstract types applied to arguments. [Text {constr; args}] is the
      application of the abstract type constructor [constr] to arguments
      [args]. *)

  | Tfarray of {
      key_ty: t;
      val_ty: t;
    }
  (** Functional arrays. [TFarray {key_ty; val_ty}] maps values of type
      [key_ty] to values of type [val_ty]. *)

  | Tsum of {
      name: Hstring.t;
      constrs: Hstring.t list
    }
  (** Enumeration, with its name, and the list of its constructors. *)

  | Tadt of {
      constr: Hstring.t;
      args: t list
    }
  (** Algebraic types applied to arguments. [Tadt {constr; args}] is the
      application of the datatype constructor [constr] to arguments [args]. *)

(** Type variables.
    The [value] field is mutated during unification,
    hence distinct types should have disjoints sets of
    type variables (see function {!val:fresh}). *)
and tvar = {
  v: int;                    (** Unique identifier. *)
  mutable value: t option;   (** Pointer to the current value of the type
                                 variable. *)
}

(** Record types. *)
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

type adt_constr = {
  constr: Hstring.t;            (** Constructor of an ADT type. *)
  destrs: (Hstring.t * t) list  (** the list of destructors associated with the
                                    constructor and their respective types *)
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

(** Hash function *)
val hash : t -> int

(** Equality function *)
val equal : t -> t -> bool

(** Comparison function *)
val compare : t -> t -> int

(** Printing function for types (does not print
    the type of each fields for records). *)
val print : t Util.printer

(** Print function for lists of types (does not print
    the type of each fields for records). *)
val print_list : t list Util.printer

(** Print function including the record fields. *)
val print_full : t Util.printer

(** Returns the set of type variables that occur in a given type. *)
val vty_of : t -> Svty.t

(** {2 Constructors} *)

(** The unit type. *)
val tunit : t

(** Generate a fresh type variable, guaranteed to be distinct
    from any other previously generated by this function. *)
val fresh_var : unit -> tvar

(** Wrap the {!val:fresh_var} function to return a type. *)
val fresh_tvar : unit -> t

(** Return a fesh abstract type. *)
val fresh_empty_text : unit -> t

(** Apply the abstract type constructor to the list of type arguments
    given. *)
val text : args:t list -> string -> t

(** [tsum ~constrs name] creates an enumeration type named [name] with
    constructors [constrs]. *)
val tsum : constrs:string list -> string -> t

(** Create an algebraic datatype. The body is a list of
    constructors, where each constructor is associated with the list of
    its destructors with their respective types. If [body] is none,
    then no definition will be registered for this type. The second
    argument is the name of the type. The third one provides its list
    of arguments. *)
val t_adt :
  ?body:((string * (string * t) list) list) option ->
  args:t list ->
  string ->
  t

(** Create a record type. [trecord args name lbs] creates a record
    type with name [name], arguments [args] and fields [lbs]. *)
val trecord :
  ?record_constr:string ->
  args:t list ->
  fields:(string * t) list ->
  string ->
  t

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

  (** Substitution application. *)
  val apply : t -> ty -> ty

  (** [union u v] applies [v] to [u], resulting in [u'].
      It then computes the union of [u'] and [v], prioritizing
      bindings from [u'] in case of conflict. *)
  val union : t -> t -> t

  (** Comparison of substitutions. *)
  val compare : t -> t -> int

  (** Equality of substitutions. *)
  val equal : t -> t -> bool

  (** Print function for substitutions. *)
  val print : t Util.printer
end

(** {2 Unification/Matching} *)

(** Exception raised during matching or unification.
    [TypeClash (u, v)] is raised when [u] and [v] could not be
    matched or unified ([u] and [v] may be sub-types of the
    types being actually unified or matched). *)
exception TypeClash of t * t

(** Destructive unification. Mutates the [value] fields of
    type variables.
    @raise TypeClash when unification is impossible. In this
      case, the [value] fields of already mutated type variables
      are left modified, which may prevent future unifications. *)
val unify : t -> t -> unit

(** Matching of types (non-destructive). [matching pat t] returns a
    substitution [subst] such that [apply_subst subst pat] is
    equal to [t]. *)
val matching : Subst.t -> t -> t -> Subst.t

(** Shorten paths in type variables values.
    Unification in particular can create chains where the [value]
    field of one type variable points to another and so on...
    This function short-circuits such chains so that the value
    of a type variable can be accessed directly. *)
val shorten : t -> t

(** {2 Manipulations on types} *)

(** Apply the given substitution, all while generating fresh variables
    for the variables not already bound in the substitution. Returns
    a substitution containing bindings from old variable to their
    fresh counterpart. *)
val fresh : t -> Subst.t -> t * Subst.t

(** Same as {!val:fresh} but on lists of types. *)
val fresh_list : t list -> Subst.t -> t list * Subst.t

(** [instantiate vars args t] builds the substitutions mapping
    each type variable in [vars] to the corresponding term in [args],
    then apply that substitution to [t].
    @raise Invalid_argument if the lists [vars] and [args]
      do not have the same length
    @raise Assertion_failure if one type in [vars] is not
      a type variable.
*)
val instantiate : t list -> t list -> t -> t

(** Return a monomorphized variant of the given type, where
    type variable without values have been replaced by abstract types. *)
val monomorphize: t -> t

(** Empties the decls cache *)
val reinit_decls : unit -> unit
