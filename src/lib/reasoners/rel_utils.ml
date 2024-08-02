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
module MX = Shostak.MXH
module SX = Shostak.SXH
module HX = Shostak.HX
module L = Xliteral
module LR = Uf.LX
module HLR = Hashtbl.Make(LR)

(** [assume_nontrivial_eqs eqs la] can be used by theories to remove from the
    equations [eqs] both duplicates and those that are implied by the
    assumptions in [la]. *)
let assume_nontrivial_eqs
    (eqs : X.r Sig_rel.input list)
    (la : X.r Sig_rel.input list)
  : X.r Sig_rel.fact list =
  match eqs with
  | [] -> []
  | eqs ->
    let table = HLR.create 17 in
    List.iter (fun (a, _, _, _) -> HLR.add table (LR.make a) ()) la;
    let eqs =
      List.fold_left
        (fun eqs ((sa, _, _, _) as e) ->
           let sa = LR.make sa in
           if HLR.mem table sa then eqs
           else (
             HLR.replace table sa ();
             e :: eqs
           )
        ) [] eqs
    in
    List.rev_map (fun (sa, _, ex, orig) -> Literal.LSem sa, ex, orig) eqs

(* The type of delayed functions. A delayed function is given an [Uf.t] instance
   for resolving expressions to semantic values, the operator to compute, and a
   list of expressions as argument.

   It returns a semantic value, and an explanation for why the operator applied
   to the arguments is equal to the result (usually derived from the
   explanations from [Uf.find]). *)
type delayed_fn =
  Uf.t -> Symbols.operator -> Expr.t list -> (X.r * Explanation.t) option

let delay1 embed is_mine f uf op = function
  | [ t ] -> (
      let r, ex = Uf.find uf t in
      match f op (embed r) with
      | Some v -> Some (is_mine v, ex)
      | None -> None
    )
  | _ -> assert false

let delay2 embed is_mine f uf op = function
  | [ t1; t2 ] -> (
      let r1, ex1 = Uf.find uf t1 in
      let r2, ex2 = Uf.find uf t2 in
      match f op (embed r1) (embed r2) with
      | Some v -> Some (is_mine v, Explanation.union ex1 ex2)
      | None -> None
    )
  | _ -> assert false

(** The [Delayed] module can be used by relations that deal with partially
    interpreted functions. It will introduce the equalities between a function
    and its interpreted value as soon as the value of its arguments become
    known.

    To avoid issues with eager splitting, functions are not computed
    on case splits unless model generation is enabled. *)
module Delayed : sig
  type t

  (** [create ~is_ready dispatch] creates a new delayed structure for the
      symbols handled by [dispatch].

      The predicate [is_ready] is used to prevent from computing the functions
      of [dispatch] before we actually know their arguments.

      [dispatch] must be pure. *)
  val create :
    is_ready:(X.r -> bool) -> (Symbols.operator -> delayed_fn option) -> t

  (** [add env uf r t] checks whether the term [t] is a delayed function and if
      so either adds it to the structure or evaluates it immediately if
      possible, in which case a new equality with corresponding explanation is
      returned.

      [r] must be the semantic value associated with [t].

      [add] can be called directly with the arguments passed to a relation's
      [add] function. *)
  val add : t -> Uf.t -> X.r -> Expr.t -> t * (X.r L.view * Explanation.t) list

  (** [update env uf r orig eqs] checks whether [r] is an argument of a
      registered delayed function and, if so, tries to compute the corresponding
      delayed function. If all the function's arguments are constants, the
      resulting equality is accumulated into [eqs].

      [update] should be called with the left-hand side of [Eq] literals that
      are [assume]d by a relation. *)
  val update :
    t -> Uf.t -> X.r -> X.r -> Th_util.lit_origin ->
    X.r Sig_rel.input list -> X.r Sig_rel.input list

  (** [assume] is a simple wrapper for [update] that is compatible with the
      [assume] signature of a relation. *)
  val assume : t -> Uf.t -> X.r Sig_rel.input list -> t * X.r Sig_rel.result

  (** [iter_delayed f t] iterates on the delayed applications of [t]. *)
  val iter_delayed : (X.r -> Symbols.operator -> Expr.t -> unit) -> t -> unit
end = struct
  module OMap = Map.Make(struct
      type t = Symbols.operator

      let compare = Symbols.compare_operators
    end)

  type t = {
    dispatch : Symbols.operator -> delayed_fn option ;
    used_by : Expr.Set.t OMap.t MX.t ;
    is_ready : X.r -> bool ;
  }

  let create ~is_ready dispatch = { dispatch; used_by = MX.empty; is_ready }

  let add ({ dispatch; used_by; _ } as env) uf r t =
    (* Note: we dispatch on [Op] symbols, but it could make sense to dispatch on
       a separate constructor for explicitely delayed terms. *)
    match Expr.term_view t with
    | { f = Op f; xs; _ } -> (
        match dispatch f with
        | None -> env, []
        | Some fn ->
          match fn uf f xs with
          | Some (r', ex) ->
            if X.equal r' r then
              (* already simplified by [X.make] *)
              env, []
            else
              env, [L.Eq(r', r), ex]
          | None ->
            let used_by =
              List.fold_left (fun used_by x ->
                  MX.update (Uf.make uf x) (fun sm ->
                      let sm = Option.value ~default:OMap.empty sm in
                      Option.some @@
                      OMap.update f (fun se ->
                          let se = Option.value ~default:Expr.Set.empty se in
                          Some (Expr.Set.add t se)) sm) used_by) used_by xs
            in { env with used_by }, []
      )
    | _ -> env, []

  let update { dispatch; used_by; _ } uf r1 eqs =
    match MX.find r1 used_by with
    | exception Not_found -> eqs
    | sm ->
      OMap.fold (fun sy se eqs ->
          let fn =
            (* The [fn] must be present because we only add symbols to
               [used_by] if they are in the dispatch table. *)
            Option.get (dispatch sy)
          in
          Expr.Set.fold (fun t eqs ->
              let { Expr.xs; f; _ } = Expr.term_view t in
              assert (Symbols.equal (Op sy) f);
              match fn uf sy xs with
              | Some (r, ex) ->
                (L.Eq (X.term_embed t, r), None, ex, Th_util.Other) :: eqs
              | None -> eqs) se eqs) sm eqs

  let update env uf r1 r2 orig eqs =
    (* The `Subst` origin is used when `r1 -> r2` is added in the union-find, so
       we want to be propagating the constant on the RHS.

       The other origins are subsumed. *)
    match orig with
    | Th_util.Subst when env.is_ready r2 -> update env uf r1 eqs
    | _ -> eqs


  let assume env uf la =
    let eqs =
      List.fold_left (fun eqs (a, _root, _expl, orig) ->
          match a with
          | Xliteral.Eq (r1, r2) -> update env uf r1 r2 orig eqs
          | _ -> eqs
        ) [] la
    in
    env, { Sig_rel.assume = assume_nontrivial_eqs eqs la; remove = [] }

  let iter_delayed f t =
    MX.iter (fun r -> OMap.iter (fun op -> Expr.Set.iter (f r op))) t.used_by
end

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

  type domain
  (** The type of domains. *)

  module Entry : sig
    type t
    (** A mutable entry associated with a given key. Can be used to access and
        update the associated domain imperatively. A single (physical) entry is
        associated with a given key. *)

    val domain : t -> domain
    (** Return the domain associated with this entry. *)

    val set_domain : t -> domain -> unit
    (** [set_domain e d] sets the domain of entry [e] to [d]. This overwrites
        any pre-existing domain associated with [e].

        {b Note}: if you need to tighten an existing domain, this must be done
        explicitely by accessing the current domain through [domain] before
        calling [set_domain].  The {!HandleNotations} module provides an
        [update] function that does this. *)
  end

  val entry : t -> key -> Entry.t
  (** [entry t k] returns the entry associated with [k].

      There is a unique entry associated with each key [k] that is created
      on-the-fly when [entry t k] is called for the first time. Calling
      [entry t k] with the same key will always return the same (physical)
      entry.

      The domain associated with the entry is initialized from the underlying
      persistent domain (or the [default] function provided to [edit]) the first
      time it is accessed, and updated with [set_domain]. *)
end

module DomainMap
    (X : ComparableType)
    (D : Domain)
  : sig
    (** A persistent map to a domain type, with an ephemeral interface. *)

    type t
    (** The type of domain maps. *)

    val pp : t Fmt.t
    (** Pretty-printer for domain maps. *)

    val empty : t
    (** The empty domain map. *)

    type key = X.t
    (** The type of keys in the map. *)

    type domain = D.t
    (** The type of per-variable domains. *)

    val find : key -> t -> domain
    (** Find the domain associated with the given key.

        @raise Not_found if there is no domain associated with the key. *)

    val add : key -> domain -> t -> t
    (** Adds a domain associated with a given key.

        {b Warning}: If the key is not constant, [add] updates the domain
        associated with the variable part of the key, and hence influences the
        domains of other keys that have the same variable part as this key. *)

    val remove : key -> t -> t
    (** Removes the domain associated with a single variable. This will
        effectively remove the domains associated with all keys that have the
        same variable part. *)

    val needs_propagation : t -> bool
    (** Returns [true] if the domain map needs propagation, i.e. if the domain
        associated with any variable has changed. *)

    module Ephemeral : EphemeralDomainMap
      with type key = key and type domain = domain

    val edit :
      notify:(key -> unit) -> default:(key -> domain) -> t -> Ephemeral.t
    (** Create an ephemeral domain map from the current domain map.

        [notify] will be called whenever the domain associated with a variable
        changes.

        The [default] argument is used to compute a default value for missing
        keys. *)

    val snapshot : Ephemeral.t -> t
    (** Convert back a (modified) ephemeral domain map into a persistent one.

        Only entries that had their value changed through [set_domain] are
        updated. *)
  end
=
struct
  module MX = X.Map
  module SX = X.Set
  module HX = X.Table

  type t =
    { domains : D.t MX.t
    ; changed : SX.t }

  type key = X.t

  type domain = D.t

  let pp ppf t =
    Fmt.iter_bindings ~sep:Fmt.semi MX.iter
      (Fmt.box @@ Fmt.pair ~sep:(Fmt.any " ->@ ") X.pp D.pp)
      ppf t.domains

  let empty =
    { domains = MX.empty
    ; changed = SX.empty }

  let find x t = MX.find x t.domains

  let remove x t =
    { domains = MX.remove x t.domains
    ; changed = SX.remove x t.changed }

  let add x d t = { t with domains = MX.add x d t.domains }

  let needs_propagation t = not (SX.is_empty t.changed)

  module Ephemeral = struct
    type key = X.t
    type domain = D.t

    module Entry = struct
      type t =
        { key : X.t
        ; notify : X.t -> unit
        ; mutable domain : D.t
        ; mutable dirty : bool
        ; dirty_cache : t X.Table.t }

      let[@inline] domain { domain ; _ } = domain

      let set_dirty entry =
        if not entry.dirty then (
          entry.dirty <- true;
          X.Table.replace entry.dirty_cache entry.key entry
        )

      let set_domain entry dom =
        set_dirty entry;
        entry.domain <- dom;
        entry.notify entry.key
    end

    type t =
      { domains : D.t X.Map.t
      ; entries : Entry.t X.Table.t
      ; dirty_cache : Entry.t X.Table.t
      ; notify : X.t -> unit
      ; default : X.t -> D.t }

    let entry t x =
      try X.Table.find t.entries x with Not_found ->
        let entry =
          { Entry.key = x
          ; notify = t.notify
          ; domain = (try X.Map.find x t.domains with Not_found -> t.default x)
          ; dirty = false
          ; dirty_cache = t.dirty_cache }
        in
        X.Table.replace t.entries x entry;
        entry
  end

  let edit ~notify ~default { domains ; changed } =
    SX.iter notify changed;

    { Ephemeral.domains
    ; entries = X.Table.create 17
    ; dirty_cache = X.Table.create 17
    ; notify
    ; default }

  let snapshot t =
    let domains =
      X.Table.fold (fun x entry t ->
          (* NB: we are in the [dirty_cache] so we know that the domain has been
             updated *)
          X.Map.add x (Ephemeral.Entry.domain entry) t
        ) t.Ephemeral.dirty_cache t.Ephemeral.domains
    in
    { domains
    ; changed = SX.empty }
end


module BinRel(X : OrderedType)(W : OrderedType) : sig
  (** This module provides a thin abstraction to keep track of binary relations
      between values of two different types. *)

  type t
  (** The type of binary relations between [X.t] and [W.t]. *)

  val empty : t
  (** The empty relation. *)

  val add : X.t -> W.t -> t -> t
  (** [add x w r] adds the tuple [(x, w)] to the relation. *)

  val add_many : X.t -> W.Set.t -> t -> t
  (** [add_many x ws t] adds the tuples [(x, w)] for each [w] in [ws]. *)

  val range : X.t -> t -> W.Set.t
  (** [range x t] returns all the watches [w] such that [(x, w)] is in the
      relation. *)

  val remove_dom : X.t -> t -> t
  (** [remove_dom x r] removes all tuples of the form [(x, _)] from the
      relation. *)

  val remove_range : W.t -> t -> t
  (** [remove_range w r] removes all tuples of the form [(_, w)] from the
      relation. *)

  val transfer_dom : X.t -> X.t -> t -> t
  (** [transfer_dom x x' r] replaces all tuples of the form [(x, w)] in the
      relation with the corresponding [(x', w)] tuple. *)

  val iter_range : X.t -> (W.t -> unit) -> t -> unit
  (** [iter_range x f r] calls [f] on all the [w] such that [(x, w)] is in the
      relation. *)

  val fold_range : X.t -> (W.t -> 'a -> 'a) -> t -> 'a -> 'a
  (** [fold_range x f r acc] folds [f] over all the [w] such that [(x, w)] is in
      the relation.*)
end = struct
  module MX = X.Map
  module MW = W.Map
  module SX = X.Set
  module SW = W.Set

  type t =
    { watches : SW.t MX.t ;
      (** Reverse map from variables to their watches. Used to trigger watches
          when a domain changes. *)

      watching : SX.t MW.t
      (** Map from watches to the variables they watch. Used to be able to
          remove watches. *)
    }

  let range x t =
    try MX.find x t.watches with Not_found -> W.Set.empty

  let empty =
    { watches = MX.empty
    ; watching = MW.empty }

  let add x w t =
    let watches =
      MX.update x (function
          | None -> Some (SW.singleton w)
          | Some ws -> Some (SW.add w ws)) t.watches
    and watching =
      MW.update w (function
          | None -> Some (SX.singleton x)
          | Some xs -> Some (SX.add x xs)) t.watching
    in
    { watches ; watching }

  let add_many x ws t =
    let watches =
      MX.update x (function
          | None -> Some ws
          | Some ws' -> Some (SW.union ws ws')) t.watches
    and watching =
      SW.fold (fun w watching ->
          MW.update w (function
              | None -> Some (SX.singleton x)
              | Some xs -> Some (SX.add x xs)) watching
        ) ws t.watching
    in
    { watches ; watching }

  let remove_range w t =
    match MW.find w t.watching with
    | xs ->
      let watches =
        SX.fold (fun x watches ->
            MX.update x (function
                | None ->
                  (* maps must be mutual inverses *)
                  assert false
                | Some ws ->
                  let ws = SW.remove w ws in
                  if SW.is_empty ws then None else Some ws
              ) watches
          ) xs t.watches
      in
      let watching = MW.remove w t.watching in
      { watches ; watching }
    | exception Not_found -> t

  let remove_dom x t =
    match MX.find x t.watches with
    | ws ->
      let watching =
        SW.fold (fun w watching ->
            MW.update w (function
                | None ->
                  (* maps must be mutual inverses *)
                  assert false
                | Some xs ->
                  let xs = SX.remove x xs in
                  if SX.is_empty xs then None else Some xs
              ) watching
          ) ws t.watching
      and watches = MX.remove x t.watches in
      { watches ; watching }
    | exception Not_found -> t

  let fold_range x f t acc =
    match MX.find x t.watches with
    | ws -> SW.fold f ws acc
    | exception Not_found -> acc

  let iter_range x f t =
    match MX.find x t.watches with
    | ws -> SW.iter f ws
    | exception Not_found -> ()

  let transfer_dom x x' t =
    match MX.find x t.watches with
    | ws ->
      let watching =
        SW.fold (fun w watching ->
            MW.update w (function
                | None ->
                  (* maps must be mutual inverses *)
                  assert false
                | Some xs ->
                  Some (SX.add x' (SX.remove x xs))
              ) watching
          ) ws t.watching
      and watches =
        MX.update x' (function
            | None -> Some ws
            | Some ws' -> Some (SW.union ws ws')
          ) (MX.remove x t.watches)
      in
      { watches ; watching }
    | exception Not_found -> t
end

(** Implementation of the [ComparableType] interface for semantic values. *)
module XComparable : ComparableType with type t = X.r = struct
  type t = X.r

  let pp = X.print

  let equal = X.equal

  let hash = X.hash

  let compare = X.hash_cmp

  module Set = SX

  module Map = MX

  module Table = HX
end

module type NormalForm = sig
  (** Module signature for normal form computation. *)

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

  type expr
  (** The underlying type of non-normalized expressions. *)

  val normal_form : expr -> t
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

module Domains_make
    (NF : NormalForm with type expr = X.r)
    (D : Domain
     with type var = NF.Composite.t
      and type atom = NF.Atom.t
      and type constant = NF.constant)
    (W : OrderedType)
  : sig
    include Uf.GlobalDomain

    val get : X.r -> t -> D.t
    (** [get r t] returns the domain associated with semantic value [r]. *)

    val watch : W.t -> X.r -> t -> t
    (** [watch w r t] associated the watch [w] with the domain of semantic value
        [r]. The watch [w] is triggered whenever the domain associated with [r]
        changes, and is preserved across substitutions (i.e. if [r] becomes
        [nr], [w] will be transfered to [nr]).

        {b Note}: The watch [w] is also immediately triggered for a first
        propagation. *)

    val unwatch : W.t -> t -> t
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

    module Ephemeral : EphemeralDomainMap
      with type key = X.r
       and type domain = D.t

    val edit :
      events:(NF.Atom.t, NF.Composite.t, W.t) events -> t -> Ephemeral.t
    (** [edit ~events t] returns an ephemeral copy of the domains for edition.

        The [events] argument is used to notify the caller about domain changes
        and watches being triggered.

        {b Note}: Any domain that has changed or watches that have been
        triggered through the persistent API (e.g. due to substitutions) are
        immediately notified through the appropriare [events] callback. *)

    val snapshot : Ephemeral.t -> t
    (** Converts back an ephemeral domain into a persistent one. *)
  end
=
struct
  module A = NF.Atom
  module C = NF.Composite

  module DMA = DomainMap(A)(D)
  module DMC = DomainMap(C)(D)

  module AW = BinRel(A)(W)
  module CW = BinRel(C)(W)

  type t =
    { atoms : DMA.t
    (* Map from atomic variables to their (non-default) domain. *)
    ; atom_watches : AW.t
    (* Map (and reverse map) from atomic variables to the watches that must be
       triggered when their domain gets updated. *)
    ; variables : A.Set.t
    (* Set of all atomic variables being tracked. *)
    ; composites : DMC.t
    (* Map from composite variables to their (non-default) domain. *)
    ; composite_watches : CW.t
    (* Map (and reverse map) from composite variables to the watches that must
       be triggered when their domain gets udpated. *)
    ; parents : C.Set.t A.Map.t
    (* Reverse map from atomic variables to the composite variables that
       contain them. Useful for structural propagation. *)
    ; triggers : W.Set.t
    (* Watches that have been triggered. They will be immediately notified
       when [edit] is called. *)
    }

  let pp ppf { atoms ; composites ; _ }  =
    DMA.pp ppf atoms;
    DMC.pp ppf composites

  let empty =
    { atoms = DMA.empty
    ; atom_watches = AW.empty
    ; variables = A.Set.empty
    ; composites = DMC.empty
    ; composite_watches = CW.empty
    ; parents = A.Map.empty
    ; triggers = W.Set.empty
    }

  type _ Uf.id += Id : t Uf.id

  let filter_ty = D.filter_ty

  exception Inconsistent = D.Inconsistent

  let watch w r t =
    let t = { t with triggers = W.Set.add w t.triggers } in
    match NF.normal_form r with
    | Constant _ -> t
    | Atom (a, _) ->
      { t with atom_watches = AW.add a w t.atom_watches }
    | Composite (c, _) ->
      { t with composite_watches = CW.add c w t.composite_watches }

  let unwatch w t =
    { atoms = t.atoms
    ; atom_watches = AW.remove_range w t.atom_watches
    ; variables = t.variables
    ; composites = t.composites
    ; composite_watches = CW.remove_range w t.composite_watches
    ; parents = t.parents
    ; triggers = t.triggers }

  let needs_propagation t =
    DMA.needs_propagation t.atoms ||
    DMC.needs_propagation t.composites ||
    not (W.Set.is_empty t.triggers)

  let[@inline] variables { variables ; _ } = variables

  let[@inline] parents { parents ; _ } = parents

  let track c parents =
    NF.fold_composite (fun a t ->
        A.Map.update a (function
            | Some cs -> Some (C.Set.add c cs)
            | None -> Some (C.Set.singleton c)
          ) t
      ) c parents

  let untrack c parents =
    NF.fold_composite (fun a t ->
        A.Map.update a (function
            | Some cs ->
              let cs = C.Set.remove c cs in
              if C.Set.is_empty cs then None else Some cs
            | None -> None
          ) t
      ) c parents

  let init r t =
    match NF.normal_form r with
    | Constant _ -> t
    | Atom (a, _) ->
      { t with variables = A.Set.add a t.variables }
    | Composite (c, _) ->
      { t with parents = track c t.parents }

  let default_atom a = D.unknown (NF.type_info a)

  let find_or_default_atom a t =
    try DMA.find a t.atoms
    with Not_found -> default_atom a

  let default_composite c = D.map_domain default_atom c

  let find_or_default_composite c t =
    try DMC.find c t.composites
    with Not_found -> default_composite c

  let find_or_default x t =
    match x with
    | NF.Constant c ->
      D.constant c
    | NF.Atom (a, o) ->
      D.add_offset (find_or_default_atom a t) o
    | NF.Composite (c, o) ->
      D.add_offset (find_or_default_composite c t) o

  let get r t = find_or_default (NF.normal_form r) t

  let subst ~ex rr nrr t =
    let rrd, ws, t =
      match NF.normal_form rr with
      | Constant _ -> invalid_arg "subst: cannot substitute a constant"
      | Atom (a, o) ->
        let variables = A.Set.remove a t.variables in
        D.add_offset (find_or_default_atom a t) o,
        AW.range a t.atom_watches,
        { t with
          atoms = DMA.remove a t.atoms ;
          atom_watches = AW.remove_dom a t.atom_watches ;
          variables }
      | Composite (c, o) ->
        let parents = untrack c t.parents in
        D.add_offset (find_or_default_composite c t) o,
        CW.range c t.composite_watches,
        { t with
          composites = DMC.remove c t.composites ;
          composite_watches = CW.remove_dom c t.composite_watches ;
          parents }
    in
    (* Add [ex] to justify that it applies to [nrr] *)
    let rrd = D.add_explanation ~ex rrd in
    let nrr_nf = NF.normal_form nrr in
    let nrrd = find_or_default nrr_nf t in
    let nnrrd = D.intersect nrrd rrd in
    (* Always trigger to ensure we check for simplifications. *)
    let t = { t with triggers = W.Set.union ws t.triggers } in
    let t =
      match nrr_nf with
      | Constant _ -> t
      | Atom (a, _) ->
        let atom_watches = AW.add_many a ws t.atom_watches in
        let variables = A.Set.add a t.variables in
        { t with atom_watches ; variables }
      | Composite (c, _) ->
        let composite_watches = CW.add_many c ws t.composite_watches in
        let parents = track c t.parents in
        { t with composite_watches ; parents }
    in
    if D.equal nnrrd nrrd then t
    else
      match nrr_nf with
      | Constant _ ->
        (* [nrrd] is [D.constant c] which must be a singleton; if we
           shrunk it, it can only be empty. *)
        assert false
      | Atom (a, o) ->
        let triggers = W.Set.union (AW.range a t.atom_watches) t.triggers in
        let atoms = DMA.add a (D.sub_offset nnrrd o) t.atoms in
        { t with atoms ; triggers }
      | Composite (c, o) ->
        let triggers =
          W.Set.union (CW.range c t.composite_watches) t.triggers
        in
        let composites = DMC.add c (D.sub_offset nnrrd o) t.composites in
        { t with composites ; triggers }

  module Ephemeral = struct
    type key = X.r
    type domain = D.t

    module Entry = struct
      type t =
        | Constant of NF.constant
        | Atom of DMA.Ephemeral.Entry.t * NF.constant
        | Composite of DMC.Ephemeral.Entry.t * NF.constant

      let domain = function
        | Constant c -> D.constant c
        | Atom (a, o) ->
          D.add_offset (DMA.Ephemeral.Entry.domain a) o
        | Composite (c, o) ->
          D.add_offset (DMC.Ephemeral.Entry.domain c) o

      let set_domain e d =
        match e with
        | Constant _ -> assert false
        | Atom (a, o) ->
          DMA.Ephemeral.Entry.set_domain a (D.sub_offset d o)
        | Composite (c, o) ->
          DMC.Ephemeral.Entry.set_domain c (D.sub_offset d o)
    end

    type t =
      { atoms : DMA.Ephemeral.t
      ; atom_watches : AW.t
      ; variables : A.Set.t
      ; composites : DMC.Ephemeral.t
      ; composite_watches : CW.t
      ; parents : C.Set.t A.Map.t }

    let entry t r =
      match NF.normal_form r with
      | NF.Constant c ->
        Entry.Constant c
      | NF.Atom (a, o) ->
        Atom (DMA.Ephemeral.entry t.atoms a, o)
      | NF.Composite (c, o) ->
        Entry.Composite (DMC.Ephemeral.entry t.composites c, o)
  end

  let edit ~events t =
    W.Set.iter events.evt_watch_trigger t.triggers;

    let notify_atom a =
      events.evt_atomic_change a;
      AW.iter_range a events.evt_watch_trigger t.atom_watches
    and notify_composite c =
      events.evt_composite_change c;
      CW.iter_range c events.evt_watch_trigger t.composite_watches
    in

    { Ephemeral.atoms =
        DMA.edit
          ~notify:notify_atom ~default:default_atom
          t.atoms
    ; atom_watches = t.atom_watches
    ; variables = t.variables
    ; composites =
        DMC.edit
          ~notify:notify_composite ~default:default_composite
          t.composites
    ; composite_watches = t.composite_watches
    ; parents = t.parents }

  let snapshot t =
    { atoms = DMA.snapshot t.Ephemeral.atoms
    ; atom_watches = t.Ephemeral.atom_watches
    ; variables = t.Ephemeral.variables
    ; composites = DMC.snapshot t.Ephemeral.composites
    ; composite_watches = t.Ephemeral.composite_watches
    ; parents = t.Ephemeral.parents
    ; triggers = W.Set.empty }
end

(** Wrapper around an ephemeral domain map to access domains associated with a
    representative computed by the [Uf] module. *)
module UfHandle
    (D : Domain)
    (DM : EphemeralDomainMap with type key = X.r and type domain = D.t)
  : sig
    include EphemeralDomainMap with type key = X.r and type domain = D.t

    val wrap : Uf.t -> DM.t -> t
  end
=
struct
  type key = X.r

  type domain = DM.domain

  module Entry = struct
    type t =
      { repr : X.r
      ; handle : DM.Entry.t
      ; explanation : Explanation.t }

    let domain { repr ; handle ; explanation = ex } =
      if Explanation.is_empty ex then DM.Entry.domain handle
      else
        D.intersect (D.unknown (X.type_info repr)) @@
        D.add_explanation ~ex (DM.Entry.domain handle)

    let set_domain { handle ; explanation = ex ; _ } d =
      DM.Entry.set_domain handle (D.add_explanation ~ex d)
  end

  type t =
    { uf : Uf.t
    ; cache : Entry.t HX.t
    ; domains : DM.t }

  let entry t r =
    try HX.find t.cache r with Not_found ->
      let r, explanation = Uf.find_r t.uf r in
      let h =
        { Entry.repr = r
        ; handle = DM.entry t.domains r
        ; explanation }
      in
      HX.replace t.cache r h; h

  let wrap uf t =
    { uf ; cache = HX.create 17 ; domains = t }
end

module HandleNotations
    (D : Domain)
    (E : EphemeralDomainMap with type domain = D.t) =
struct
  let (!!) = E.Entry.domain

  let update ~ex entry domain =
    let current = E.Entry.domain entry in
    let domain = D.intersect current (D.add_explanation ~ex domain) in
    if not (D.equal domain current) then
      E.Entry.set_domain entry domain
end
