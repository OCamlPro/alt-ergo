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
(*     More details can be found in the directory licenses/               *)
(*                                                                        *)
(**************************************************************************)

(** The [name_space] type discriminates the different types of internal
    identifiers. The same string in different name spaces is considered as
    different identifiers.

    Note that the identifier stored in the [Hstring] constructor below are
    mangled during its creation: a special prefix is added depending on the
    name space. *)
type name_space =
  | Internal
  (** This symbol is an internal implementation detail of the solver, such as
      a proxy formula or the abstracted counterpart of AC symbols.

      Internal identifiers are printed with a ".!" prefix. *)
  | Fresh
  (** This symbol is a "fresh" internal identifer. Fresh internal identifiers
      play a similar role as internal identifiers, but they always represent a
      constant that was introduced during solving as part of some kind of
      purification or abstraction procedure.

      In order to correctly implement AC(X) in the presence of distributive
      symbols, symbols generated for AC(X) abstraction use a special
      namespace, [Fresh_ac] below.

      To ensure uniqueness, fresh identifiers must always be generated using
      [Id.Namespace.Internal.fresh ()].

      In particular, fresh identifiers are only used to denote constants, not
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

      To ensure uniqueness, AC abstraction identifiers must always be generated
      using [fresh ~ns:Fresh_ac ()]. *)
  | Skolem
  (** This symbol has been introduced as part of skolemization, and represents
      the (dependent) variable of an existential quantifier. Skolem identifiers
      can have arbitrary arity to depend on previous skolem names in binding
      order (so if you have `(exists (x y) e)` then there will be a skolem
      variable `sko_x` and a skolem function `(sko_y sko_x)`). *)
  | Abstract
  (** This symbol has been introduced as part of model generation, and
      represents an abstract value.

      To ensure uniqueness, abstract identifiers must always be generated using
      [fresh ~ns:Abstract ()]. *)

type t = private
  | Term_cst of { tcst : Dolmen.Std.Expr.term_cst; defined : bool }
  (** This identifier was declared or defined by the user, and appears as is
      somewhere in a source file. *)

  | Hstring of { hs : Hstring.t; ns : name_space }

(* TODO: remove this type after replacing Alt-Ergo types by Dolmen types. *)
type typed = Dolmen.Std.Expr.term_cst * Ty.t list * Ty.t
val compare_typed : typed -> typed -> int

val of_term_cst : ?defined:bool -> Dolmen.Std.Expr.term_cst -> t
(** [of_term_cst ?defined t] creates an identifier from a constant term.
    The argument [defined] is used to determine if the identifier is
    declared or defined by user. *)

val of_string : ns:name_space -> string -> t
(** [of_string ~ns s] creates an identifier in the name space [ns] from the
    string [s].

    Note that identifiers are pre-mangled: the [hs] field of the resulting
    identifier may not be exactly the string that was passed to this function
    (however, calling [of_string] with the same string but two different name
    spaces is guaranteed to return two identifiers with distinct [hs] fields).

    @raise Invalid_argument if the name space is [Fresh], [Fresh_ac] or
           [Abstract]. *)

val fresh : ?base:string -> ns:name_space -> unit -> t
(** [fresh ?base ~ns ()] generates a fresh identifier within the name space [ns]
    derived from the base string [base]. If [base] is not provided, an empty
    string is used by default.

    The identifier is pre-mangled similarly to [of_string]. *)

val compare : t -> t -> int
(** [compare i1 i2] compares the identifiers [i1] and [i2]. *)

val equal : t -> t -> bool
(** [equal i1 i2] checks if [i1] and [i2] are equal. *)

val hash : t -> int
(** [hash i] computes a hash for the identifier [i]. On term constant
    identifiers, this hash is perfect. *)

val pp : t Fmt.t
(** [pp ppf i] prints the identifier [i] on the formatter [ppf], quoting the
    string, if it needs. *)

val show : t -> string
(** Same as [pp] but outputs the result as a string. *)

val is_suspicious : t -> bool

val reinit : unit -> unit
(** Resets the internal counters of the [fresh] function. *)

module Map : Map.S with type key = t
