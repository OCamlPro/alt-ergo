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

module DomainMap
    (X : Domains_intf.ComparableType)
    (D : Domains_intf.Domain)
  : Domains_intf.DomainMap with type key = X.t and type domain = D.t
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

    module Entry = struct
      type domain = D.t

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

    let ( !! ) = Entry.domain

    let update ~ex entry domain =
      let current = !!entry in
      let domain = D.intersect current (D.add_explanation ~ex domain) in
      if not (D.equal domain current) then
        Entry.set_domain entry domain
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


module WatchMap(X : Domains_intf.OrderedType)(W : Domains_intf.OrderedType)
  : sig
    (** This module provides a thin abstraction to keep track of
        "watchers" associated to a given variable.

        It allows finding all the watches associated to a variable, and
        conversely of all the variable associated with a watch. *)

    type t
    (** The type of maps from variables [X.t] to watches [W.t]. *)

    val empty : t
    (** The empty relation. *)

    val add_watches : X.t -> W.Set.t -> t -> t
    (** [add_watches x ws t] associates all of the watches in [ws] to the
        variable [x]. *)

    val watches : X.t -> t -> W.Set.t
    (** [watches x t] returns all the watches associated to [x]. *)

    val take_watches : X.t -> t -> W.Set.t * t
    (** [take_watches x t] returns a pair [ws, t'] where [ws] is the set of
        watches associated with [x] in [t], and [t'] is identical to [t]
        except that no watches are associated to [x]. *)

    val remove_watch : W.t -> t -> t
    (** [remove_watch w t] removes [w] from [t] so that it is no longer
        associated to any variable. *)
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

  let empty =
    { watches = MX.empty
    ; watching = MW.empty }

  let add_watches x ws t =
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

  let remove_watch w t =
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

  let watches x t =
    try MX.find x t.watches with Not_found -> W.Set.empty

  let take_watches x t =
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
      ws, { watches ; watching }
    | exception Not_found -> W.Set.empty, t
end

(** Implementation of the [ComparableType] interface for semantic values. *)
module XComparable : Domains_intf.ComparableType with type t = X.r = struct
  type t = X.r

  let pp = X.print

  let equal = X.equal

  let hash = X.hash

  let compare = X.hash_cmp

  module Set = SX

  module Map = MX

  module Table = HX
end

module Domains_make
    (NF : Domains_intf.NormalForm)
    (D : Domains_intf.Domain
     with type var = NF.Composite.t
      and type atom = NF.Atom.t
      and type constant = NF.constant)
    (W : Domains_intf.OrderedType)
  : Domains_intf.S
    with module NF := NF
     and type domain := D.t
     and type watch := W.t
=
struct
  module A = NF.Atom
  module C = NF.Composite

  module DMA = DomainMap(A)(D)
  module DMC = DomainMap(C)(D)

  module AW = WatchMap(A)(W)
  module CW = WatchMap(C)(W)

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
      { t with
        atom_watches =
          AW.add_watches a (W.Set.singleton w) t.atom_watches }
    | Composite (c, _) ->
      { t with
        composite_watches =
          CW.add_watches c (W.Set.singleton w) t.composite_watches }

  let unwatch w t =
    { atoms = t.atoms
    ; atom_watches = AW.remove_watch w t.atom_watches
    ; variables = t.variables
    ; composites = t.composites
    ; composite_watches = CW.remove_watch w t.composite_watches
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
        let ws, atom_watches = AW.take_watches a t.atom_watches in
        D.add_offset (find_or_default_atom a t) o,
        ws,
        { t with
          atoms = DMA.remove a t.atoms ;
          atom_watches ;
          variables }
      | Composite (c, o) ->
        let parents = untrack c t.parents in
        let ws, composite_watches = CW.take_watches c t.composite_watches in
        D.add_offset (find_or_default_composite c t) o,
        ws,
        { t with
          composites = DMC.remove c t.composites ;
          composite_watches ;
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
        let atom_watches = AW.add_watches a ws t.atom_watches in
        let variables = A.Set.add a t.variables in
        { t with atom_watches ; variables }
      | Composite (c, _) ->
        let composite_watches = CW.add_watches c ws t.composite_watches in
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
        let triggers =
          W.Set.union (AW.watches a t.atom_watches) t.triggers
        in
        let atoms = DMA.add a (D.sub_offset nnrrd o) t.atoms in
        { t with atoms ; triggers }
      | Composite (c, o) ->
        let triggers =
          W.Set.union (CW.watches c t.composite_watches) t.triggers
        in
        let composites = DMC.add c (D.sub_offset nnrrd o) t.composites in
        { t with composites ; triggers }

  module Ephemeral = struct
    type key = X.r

    module Entry = struct
      type domain = D.t

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

    let ( !! ) = Entry.domain

    let update ~ex entry domain =
      let current = !!entry in
      let domain = D.intersect current (D.add_explanation ~ex domain) in
      if not (D.equal domain current) then
        Entry.set_domain entry domain

    module Canon = struct
      type key = X.r

      module Entry = struct
        type domain = D.t

        type t =
          { repr : X.r
          ; entry : Entry.t
          ; explanation : Explanation.t }

        let domain { repr ; entry ; explanation = ex } =
          if Explanation.is_empty ex then Entry.domain entry
          else
            D.intersect (D.unknown (X.type_info repr)) @@
            D.add_explanation ~ex (Entry.domain entry)

        let set_domain { entry ; explanation = ex ; _ } d =
          Entry.set_domain entry (D.add_explanation ~ex d)
      end

      type nonrec t =
        { uf : Uf.t
        ; cache : Entry.t HX.t
        ; domains : t }

      let entry t r =
        try HX.find t.cache r with Not_found ->
          let r, explanation = Uf.find_r t.uf r in
          let h =
            { Entry.repr = r
            ; entry = entry t.domains r
            ; explanation }
          in
          HX.replace t.cache r h; h

      let ( !! ) = Entry.domain

      let update ~ex entry domain =
        let current = !!entry in
        let domain = D.intersect current (D.add_explanation ~ex domain) in
        if not (D.equal domain current) then
          Entry.set_domain entry domain
    end

    let canon uf domains =
      { Canon.uf ; cache = HX.create 17 ; domains }
  end

  let edit ~events t =
    W.Set.iter events.Domains_intf.evt_watch_trigger t.triggers;

    let notify_atom a =
      events.evt_atomic_change a;
      W.Set.iter events.evt_watch_trigger (AW.watches a t.atom_watches);
    and notify_composite c =
      events.evt_composite_change c;
      W.Set.iter events.evt_watch_trigger (CW.watches c t.composite_watches);
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
