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

open Domains_intf

module X = Shostak.Combine
module MX = Shostak.MXH
module SX = Shostak.SXH
module HX = Shostak.HX

module DomainMap
    (X : ComparableType)
    (D : Domain)
    (W : OrderedType) :
sig
  (** A persistent map to a domain type, with an ephemeral interface.

      This is used to encapsulate some of the logic of the [Make] functor below.

      A domain map maps variables of type [X.t] to domains of type [D.t]. It
      also keeps track of "watches" of type [W.t]: arbitrary object associated
      with one or several variables. Typically, watches represent constraints
      that involve the corresponding variable; they are tracked so that the
      constraints can be marked for propagation as needed.
  *)

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

  module Ephemeral : EphemeralDomainMap
    with type key = key and type Entry.domain = domain

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

  val add_watches : key -> W.Set.t -> t -> t
  (** [add_watches x ws t] associates all the watches in [ws] with the variable
      [x].*)

  val remove_watch : W.t -> t -> t
  (** [remove_watch w t] removes the watch from all the variables it is
      associated with. *)

  val watches : key -> t -> W.Set.t
  (** Returns the set of watches associated with object [x]. *)

  val needs_propagation : t -> bool
  (** Returns [true] if the domain needs propagation. This means that the domain
      associated with some variables has been shrunk, and cross-domain
      propagation might be needed. *)
end
=
struct
  module MX = X.Map
  module SX = X.Set
  module HX = X.Table

  type t =
    { domains : D.t MX.t
    (** Map from variables to their domain. *)
    ; watches : W.Set.t MX.t
    (** Reverse map from variables to their watches. Used to trigger
        watches when a domain changes. *)
    ; watching : SX.t W.Map.t
    (** Map from watches to the variables they watch. Used to be able
        to remove watches. *)
    ; changed : SX.t
    (** Set of variables whose domain has changed. Used for cross-domain
        propagations.*)
    }

  type key = X.t

  type domain = D.t

  let pp ppf t =
    Fmt.iter_bindings ~sep:Fmt.semi MX.iter
      (Fmt.box @@ Fmt.pair ~sep:(Fmt.any " ->@ ") X.pp D.pp)
      ppf t.domains

  let empty =
    { domains = MX.empty
    ; watches = MX.empty
    ; watching = W.Map.empty
    ; changed = SX.empty }

  let find x t = MX.find x t.domains

  let remove x t =
    let domains = MX.remove x t.domains in
    let watches, watching =
      match MX.find x t.watches with
      | ws ->
        let watching =
          W.Set.fold (fun w watching ->
              W.Map.update w (function
                  | None ->
                    (* maps must be mutual inverses *)
                    assert false
                  | Some xs ->
                    let xs = SX.remove x xs in
                    if SX.is_empty xs then None else Some xs
                ) watching
            ) ws t.watching
        in
        MX.remove x t.watches, watching
      | exception Not_found -> t.watches, t.watching
    in
    let changed = SX.remove x t.changed in
    { domains ; watches ; watching ; changed }

  let add_watches x ws t =
    let watches =
      MX.update x (function
          | None -> Some ws
          | Some ws' -> Some (W.Set.union ws ws')) t.watches
    and watching =
      W.Set.fold (fun w watching ->
          W.Map.update w (function
              | None -> Some (SX.singleton x)
              | Some xs -> Some (SX.add x xs)) watching
        ) ws t.watching
    in
    { domains = t.domains ; watches ; watching ; changed = t.changed }

  let remove_watch w t =
    match W.Map.find w t.watching with
    | xs ->
      let watches =
        SX.fold (fun x watches ->
            MX.update x (function
                | None ->
                  (* maps must be mutual inverses *)
                  assert false
                | Some ws ->
                  let ws = W.Set.remove w ws in
                  if W.Set.is_empty ws then None else Some ws
              ) watches
          ) xs t.watches
      in
      let watching = W.Map.remove w t.watching in
      { domains = t.domains ; watches ; watching ; changed = t.changed }
    | exception Not_found -> t

  let watches x t =
    try MX.find x t.watches with Not_found -> W.Set.empty

  let add x d t =
    { t with domains = MX.add x d t.domains ; changed = SX.add x t.changed }

  let needs_propagation t =
    not (SX.is_empty t.changed)

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
      ; watches : W.Set.t MX.t
      ; watching : SX.t W.Map.t
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

  let edit ~notify ~default { domains ; watches ; watching ; changed } =
    SX.iter notify changed;
    { Ephemeral.domains
    ; watches
    ; watching
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
    ; watches = t.Ephemeral.watches
    ; watching = t.Ephemeral.watching
    ; changed = SX.empty }
end

module Make
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

  module DMA = DomainMap(A)(D)(W)
  module DMC = DomainMap(C)(D)(W)

  type t =
    { atoms : DMA.t
    (* Map from atomic variables to their (non-default) domain. *)
    ; variables : A.Set.t
    (* Set of all atomic variables being tracked. *)
    ; composites : DMC.t
    (* Map from composite variables to their (non-default) domain. *)
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
    ; variables = A.Set.empty
    ; composites = DMC.empty
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
        atoms = DMA.add_watches a (W.Set.singleton w) t.atoms }
    | Composite (c, _) ->
      { t with
        composites = DMC.add_watches c (W.Set.singleton w) t.composites }

  let unwatch w t =
    { atoms = DMA.remove_watch w t.atoms
    ; variables = t.variables
    ; composites = DMC.remove_watch w t.composites
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
        let ws = DMA.watches a t.atoms in
        let atoms = DMA.remove a t.atoms in
        D.add_offset (find_or_default_atom a t) o,
        ws,
        { t with atoms ; variables }
      | Composite (c, o) ->
        let parents = untrack c t.parents in
        let ws = DMC.watches c t.composites in
        let composites = DMC.remove c t.composites in
        D.add_offset (find_or_default_composite c t) o,
        ws,
        { t with composites ; parents }
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
        let variables = A.Set.add a t.variables in
        let atoms = DMA.add_watches a ws t.atoms in
        { t with atoms ; variables }
      | Composite (c, _) ->
        let parents = track c t.parents in
        let composites = DMC.add_watches c ws t.composites in
        { t with composites ; parents }
    in
    if D.equal nnrrd nrrd then t
    else
      match nrr_nf with
      | Constant _ ->
        (* [nrrd] is [D.constant c] which must be a singleton; if we
           shrunk it, it can only be empty. *)
        assert false
      | Atom (a, o) ->
        let triggers = W.Set.union (DMA.watches a t.atoms) t.triggers in
        let atoms = DMA.add a (D.sub_offset nnrrd o) t.atoms in
        { t with atoms ; triggers }
      | Composite (c, o) ->
        let triggers = W.Set.union (DMC.watches c t.composites) t.triggers in
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
      ; variables : A.Set.t
      ; composites : DMC.Ephemeral.t
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

        let set_domain { repr ; entry ; explanation = ex } d =
          if Explanation.is_empty ex then Entry.set_domain entry d
          else
            Entry.set_domain entry @@
            D.intersect (D.unknown (X.type_info repr)) @@
            D.add_explanation ~ex d
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
    W.Set.iter events.evt_watch_trigger t.triggers;

    let notify_atom a =
      events.evt_atomic_change a;
      W.Set.iter events.evt_watch_trigger (DMA.watches a t.atoms);
    and notify_composite c =
      events.evt_composite_change c;
      W.Set.iter events.evt_watch_trigger (DMC.watches c t.composites);
    in

    { Ephemeral.atoms =
        DMA.edit
          ~notify:notify_atom ~default:default_atom
          t.atoms
    ; variables = t.variables
    ; composites =
        DMC.edit
          ~notify:notify_composite ~default:default_composite
          t.composites
    ; parents = t.parents }

  let snapshot t =
    { atoms = DMA.snapshot t.Ephemeral.atoms
    ; variables = t.Ephemeral.variables
    ; composites = DMC.snapshot t.Ephemeral.composites
    ; parents = t.Ephemeral.parents
    ; triggers = W.Set.empty }
end
