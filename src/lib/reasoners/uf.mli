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

(** {1 Uf module} *)

type t

type r = Shostak.Combine.r

type _ id = ..
(** Extensible type for global domains identifiers, see {!GlobalDomains}. *)

val src : Logs.src

module type GlobalDomain = sig
  (** Module signature for global domains used by the union-find module.

      A global domain records a set of potentially correlated values for
      multiple variables at once. This is typically, but not necessarily, an
      associative mapping of variables to their own independent domain.

      {b Note}: This module signature only contains the bare minimum for
      interaction with the union-find module to be able to update the global
      domains appropriately when new terms are introduced and equivalence
      classes are merged. In particular, it purposefully provides no facility
      to access or modify the global domain to allow more flexibility in the
      to the implementer. *)

  type t
  (** The type of global domains. *)

  val pp : t Fmt.t
  (** Pretty-printer for global domains. *)

  type _ id += Id : t id
  (** Unique identifier for this module. Used for dispatch by the union-find.

      {b Warning}: This identifier must be unique; do not re-export the [Id]
      from another module (e.g. through [include]). *)

  val empty : t
  (** The empty domain. *)

  val filter_ty : Ty.t -> bool
  (** Limit the type of terms that this module cares about. Only substitutions
      of representatives for which [filter_ty (type_info r)] holds will be
      propagated to this module. *)

  val init : r -> t -> t
  (** [init r t] is called when the representative [r] is added to the
      union-find, if it has a type that matches [filter_ty].

      {b Note}: unlike [Relation.add], this function is called even for
      "dynamic" representatives added by [X.make] or AC normalization. *)

  exception Inconsistent of Explanation.t
  (** Raised by [subst] below when an inconsistency is found while merging the
      domains. *)

  val subst : ex:Explanation.t -> r -> r -> t -> t
  (** [subst ~ex rr nrr t] is called when the representatives [rr] and [nrr] are
      merged with explanation [ex]. [nrr] is the new representative; [rr] should
      no longer be tracked and the intersection of domains should be associated
      with [nrr].

      The explanation [ex] justifies the equality [rr = nrr].

      @raise Inconsistent if the domains for [rr] and [nrr] are incompatible. *)
end

type 'a global_domain = (module GlobalDomain with type t = 'a)
(** The type of global domain modules with a given storage type (see
    {!GlobalDomain}). *)

module GlobalDomains : sig
  (** This module provides a registry type to access and update a single
      "current" instance associated with multiple global domain types. *)

  type t
  (** Maps global domain modules (of type ['a global_domain]) to an
      associated domain of the corresponding type ['a]. *)

  val empty : t
  (** [empty] maps all domain modules [D] to their default domain [D.empty]. *)

  val find : 'a global_domain -> t -> 'a
  (** [find (module D) t] returns the global domain associated with the domain
      module [D]. Defaults to [D.empty]. *)

  val add : 'a global_domain -> 'a -> t -> t
  (** [add (module D) d t] registers the global domain [d] for the domain module
      [D]. Overwrite any pre-existing global domain associated with [D]. *)
end

module LX = Shostak.L

val empty : t
val add : t -> Expr.t -> t * Expr.t list

val mem : t -> Expr.t -> bool

val find : t -> Expr.t -> r * Explanation.t

val find_r : t -> r -> r * Explanation.t

val domains : t -> GlobalDomains.t

val set_domains : t -> GlobalDomains.t -> t

val union :
  t -> r -> r -> Explanation.t ->
  t * (r * (r * r * Explanation.t) list * r) list

val distinct : t -> r list -> Explanation.t -> t

val are_equal : t -> Expr.t -> Expr.t -> added_terms:bool -> Th_util.answer
val are_distinct : t -> Expr.t -> Expr.t -> Th_util.answer
val already_distinct : t -> r list -> bool

val class_of : t -> Expr.t -> Expr.Set.t
val rclass_of : t -> r -> Expr.Set.t

val cl_extract : t -> Expr.Set.t list

val print : t -> unit
val term_repr : t -> Expr.t -> Expr.t

val make : t -> Expr.t -> r (* may raise Not_found *)

val is_normalized : t -> r -> bool

val assign_next : t -> (r Xliteral.view * bool * Th_util.lit_origin) list * t

(** {2 Counterexample function} *)

(** Compute a counterexample using the Uf environment *)
val extract_concrete_model :
  prop_model:Expr.Set.t ->
  declared_ids:Id.typed list ->
  t ->
  Models.t

(** saves the module's cache *)
val save_cache : unit -> unit

(** reinitializes the module's cache with the saved one *)
val reinit_cache : unit -> unit
