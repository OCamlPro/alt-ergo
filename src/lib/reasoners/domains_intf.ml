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

module X = Shostak.Combine

module type OrderedType = sig
  (** Module signature for an ordered type equipped with a [compare] function.

      This is similar to [Set.OrderedType] and [Map.OrderedType], but includes
      pre-built [Set] and [Map] modules. *)

  type t

  val pp : t Fmt.t

  val compare : t -> t -> int

  module Set : Set.S with type elt = t

  module Map : Map.S with type key = t
end

module type ComparableType = sig
  (** Module signature combining [OrderedType] and [Hashtbl.HashedType].

      This includes a pre-built [Table] module that implements the [Hashtbl.S]
      signature. *)

  include OrderedType

  val equal : t -> t -> bool

  val hash : t -> int

  module Table : Hashtbl.S with type key = t
end

module type Domain = sig
  type t
  (** The type of domains for a single value.

      This is an abstract type that is instanciated by the theory. Note that
      it is expected that this type can carry explanations. *)

  val equal : t -> t -> bool
  (** [equal d1 d2] returns [true] if the domains [d1] and [d2] are
      identical.  Explanations should not be taken into consideration, i.e.
      two domains with different explanations but identical semantics content
      should compare equal. *)

  val pp : t Fmt.t
  (** Pretty-printer for domains. *)

  exception Inconsistent of Explanation.t
  (** Exception raised by [intersect] when an inconsistency is detected. *)

  val filter_ty : Ty.t -> bool
  (** Filter for the types of values this domain can be attached to. *)

  type constant
  (** The type of constant values. *)

  val constant : constant -> t
  (** [constant c] returns the singleton domain {m \{ c \}}. *)

  val unknown : Ty.t -> t
  (** [unknown ty] returns a full domain for values of type [t].

      @raises Invalid_argument if [filter_ty ty] does not hold. *)

  val add_explanation : ex:Explanation.t -> t -> t
  (** [add_explanation ~ex d] adds the justification [ex] to the domain d. The
      returned domain is identical to the domain of [d], only the
      justifications are changed. *)

  val intersect : t -> t -> t
  (** [intersect d1 d2] returns a new domain [d] that subsumes both [d1]
      and [d2]. Any explanation justifying that [d1] and [d2] apply to the
      same value must have been added to [d1] and [d2].

      @raise Inconsistent if [d1] and [d2] are not compatible (the
      intersection would be empty). *)

  val add_offset : t -> constant -> t
  (** [add_offset ofs d] adds the offset [ofs] to domain [d]. *)

  val sub_offset : t -> constant -> t
  (** [sub_offset ofs d] removes the offset [ofs] from domain [d]. *)

  type var
  (** The type of (composite) variable this domain applies to. *)

  type atom
  (** The type of atomic variables this domain applies to. *)

  val map_domain : (atom -> t) -> var -> t
  (** [map_domain f c] constructs a domain for a composite variable [c] from a
      function [f] that returns the domain of an atom. *)
end

module type EphemeralDomainMap = sig
  (** This module provides a signature for ephemeral domain maps: imperative
      mappings from some key type to a domain type. *)

  type t
  (** The type of ephemeral domain maps, i.e. an imperative structure mapping
      keys to their current domain. *)

  type key
  (** The type of keys in the ephemeral map. *)

  module Entry : sig
    type t
    (** A mutable entry associated with a given key. Can be used to access and
        update the associated domain imperatively. A single (physical) entry is
        associated with a given key. *)

    type domain
    (** The type of domains associated with an entry. *)

    val domain : t -> domain
    (** Return the domain associated with this entry. *)

    val set_domain : t -> domain -> unit
    (** [set_domain e d] sets the domain of entry [e] to [d]. This overwrites
        any pre-existing domain associated with [e].

        {b Note}: the caller is responsible for ensuring that the domain is
        a subset of the possible domains for the entry (e.g. due to type
        constraints). The recommended way to do so is by first intersecting
        with the existing [domain]. See also the {!EntryNotation} functor
        which does this for you. *)
  end

  val entry : t -> key -> Entry.t
  (** [entry t k] returns the entry associated with [k].

      There is a unique entry associated with each key [k] that is created
      on-the-fly when [entry t k] is called for the first time. Calling
      [entry t k] with the same key will always return the same (physical)
      entry.

      The domain associated with the entry is initialized from the underlying
      persistent domain (or the [default] function provided to [edit]) the first
      time it is accessed, and updated with [set_domain] or [update]. *)
end

module type EntryNotation = sig
  type entry
  (** The type of entries that hold a mutable reference to a domain. *)

  type domain
  (** The type of domains. *)

  val ( !! ) : entry -> domain
  (** Return the domain associated with this entry. *)

  val update : ex:Explanation.t -> entry -> domain -> unit
  (** [update ~ex e d] updates the domain associated with [e], intersecting it
      with [d]. The explanation [ex] is added to [d].

      @raises Domain.Inconsistent if the domains are incompatible. *)
end

module type NormalForm = sig
  (** Module signature for normal form computations. *)

  type constant
  (** The type of constant values. *)

  module Atom : ComparableType
  (** Atomic variables cannot be decomposed further. *)

  val type_info : Atom.t -> Ty.t
  (** [type_info a] returns the type of atomic variable [x]. *)

  module Composite : ComparableType
  (** Composite variables are obtained through a combination of
      atomic variables (e.g. a multi-variate polynomial). *)

  val fold_composite : (Atom.t -> 'a -> 'a) -> Composite.t -> 'a -> 'a
  (** [fold_composite f c acc] folds [f] over all the atoms that make up [c]. *)

  type t =
    | Constant of constant
    (** A constant value. *)
    | Atom of Atom.t * constant
    (** An atomic variable with a constant offset. *)
    | Composite of Composite.t * constant
    (** A composite variable with a constant offset. *)
  (** The type of normal forms. *)

  val normal_form : X.r -> t
  (** [normal_form e] computes the normal form of expression [e]. *)
end

type ('a, 'c, 'w) events =
  { evt_atomic_change : 'a -> unit
  ; evt_composite_change : 'c -> unit
  (** Called by the ephemeral interface when the domain associated with a
      variable changes. *)
  ; evt_watch_trigger : 'w -> unit
  (** Called by the ephemeral interface when a watcher is triggered. *)
  }
(** Handlers for events used by the ephemeral interface. *)

module type S = sig
  module NF : NormalForm
  (** The type of semantic value normal forms. *)

  type domain
  (** The type of domains associated with semantic values. *)

  type watch
  (** The type of watches to notify when domains change. *)

  include Uf.GlobalDomain

  val get : X.r -> t -> domain
  (** [get r t] returns the domain associated with semantic value [r]. *)

  val watch : watch -> X.r -> t -> t
  (** [watch w r t] associated the watch [w] with the domain of semantic value
      [r]. The watch [w] is triggered whenever the domain associated with [r]
      changes, and is preserved across substitutions (i.e. if [r] becomes
      [nr], [w] will be transfered to [nr]).

      {b Note}: The watch [w] is also immediately triggered for a first
      propagation. *)

  val unwatch : watch -> t -> t
  (** [unwatch w] removes [w] from all watch lists. It will no longer be
      triggered.

      {b Note}: If [w] has already been triggered, it is not removed from the
      triggered list. *)

  val needs_propagation : t -> bool
  (** Returns [true] if the domains needs propagation, i.e. if any variable's
      domain has changed. *)

  val variables : t -> NF.Atom.Set.t
  (** Returns the set of atomic variables that are currently being tracked. *)

  val parents : t -> NF.Composite.Set.t NF.Atom.Map.t
  (** Returns a map from atomic variables to all the composite variables that
      contain them and are currently being tracked. *)

  module Ephemeral : sig
    include EphemeralDomainMap
      with type key = X.r and type Entry.domain = domain

    include EntryNotation
      with type entry := Entry.t and type domain := domain

    (** The [Canon] module first computes the canonical representative in an
        [Uf.t] instance before accessing the ephemeral map. *)
    module Canon : sig
      include EphemeralDomainMap
        with type key = X.r and type Entry.domain = domain

      include EntryNotation
        with type entry := Entry.t and type domain := domain
    end

    val canon : Uf.t -> t -> Canon.t
    (** Wraps the ephemeral domain map to first compute the canonical
        representative in the current union-find environment prior to
        accessing the ephemeral map.

        {b Note}: The canonical map shares the same mutable space with the
        original map. *)
  end

  val edit :
    events:(NF.Atom.t, NF.Composite.t, watch) events -> t -> Ephemeral.t
  (** [edit ~events t] returns an ephemeral copy of the domains for edition.

      The [events] argument is used to notify the caller about domain changes
      and watches being triggered.

      {b Note}: Any domain that has changed or watches that have been
      triggered through the persistent API (e.g. due to substitutions) are
      immediately notified through the appropriare [events] callback. *)

  val snapshot : Ephemeral.t -> t
  (** Converts back an ephemeral domain into a persistent one. *)
end
