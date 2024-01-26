(**************************************************************************)
(*                                                                        *)
(*     Alt-Ergo: The SMT Solver For Software Verification                 *)
(*     Copyright (C) 2013-2023 --- OCamlPro SAS                           *)
(*                                                                        *)
(*     This file is distributed under the terms of OCamlPro               *)
(*     Non-Commercial Purpose License, version 1.                         *)
(*                                                                        *)
(*     As an exception, Alt-Ergo Club members at the Gold level can       *)
(*     use this file under the terms of the Apache Software License       *)
(*     version 2.0.                                                       *)
(*                                                                        *)
(*     More details can be found in the directory licenses/               *)
(*                                                                        *)
(**************************************************************************)

module X = Shostak.Combine
module MX = Shostak.MXH
module SX = Shostak.SXH
module L = Xliteral
module LR = Uf.LX
module SR = Set.Make(
  struct
    type t = X.r L.view
    let compare a b = LR.compare (LR.make a) (LR.make b)
  end)

(** [assume_nontrivial_eqs eqs la] can be used by theories to remove from the
    equations [eqs] both duplicates and those that are implied by the
    assumptions in [la]. *)
let assume_nontrivial_eqs
    (eqs : X.r Sig_rel.input list)
    (la : X.r Sig_rel.input list)
  : X.r Sig_rel.fact list =
  let la =
    List.fold_left (fun m (a, _, _, _) -> SR.add a m) SR.empty la
  in
  let eqs, _ =
    List.fold_left
      (fun ((eqs, m) as acc) ((sa, _, _, _) as e) ->
         if SR.mem sa m then acc else e :: eqs, SR.add sa m
      )([], la) eqs
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

  (** [create dispatch] creates a new delayed structure for the symbols handled
      by [dispatch].

      [dispatch] must be pure. *)
  val create : (Symbols.operator -> delayed_fn option) -> t

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
end = struct
  module OMap = Map.Make(struct
      type t = Symbols.operator

      let compare = Symbols.compare_operators
    end)

  type t = {
    dispatch : Symbols.operator -> delayed_fn option ;
    used_by : Expr.Set.t OMap.t MX.t ;
  }

  let create dispatch = { dispatch; used_by = MX.empty }

  let add ({ dispatch; used_by } as env) uf r t =
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

  let update { dispatch; used_by } uf r1 eqs =
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
    | Th_util.Subst when X.is_constant r2 -> update env uf r1 eqs
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

  val unknown : Ty.t -> t
  (** [unknown ty] returns a full domain for values of type [t]. *)

  val add_explanation : ex:Explanation.t -> t -> t
  (** [add_explanation ~ex d] adds the justification [ex] to the domain d. The
      returned domain is identical to the domain of [d], only the
      justifications are changed. *)

  val intersect : ex:Explanation.t -> t -> t -> t
  (** [intersect ~ex d1 d2] returns a new domain [d] that subsumes both [d1]
      and [d2]. The explanation [ex] justifies that the two domains can be
      merged.

      @raise Inconsistent if [d1] and [d2] are not compatible (the
      intersection would be empty). The justification always includes the
      justification [ex] used for the intersection. *)


  val fold_leaves : (X.r -> t -> 'a -> 'a) -> X.r -> t -> 'a -> 'a
  (** [fold_leaves f r t acc] folds [f] over the leaves of [r], deconstructing
      the domain [t] according to the structure of [r].

      It is assumed that [t] already contains any justification required for
      it to apply to [r].

      @raise Inconsistent if [r] cannot possibly be in the domain of [t]. *)

  val map_leaves : (X.r -> 'a -> t) -> X.r -> 'a -> t
  (** [map_leaves f r acc] is the "inverse" of [fold_leaves] in the sense that
      it rebuilds a domain for [r] by using [f] to access the domain for each
      of [r]'s leaves. *)
end

module type Domains = sig
  type t
  (** The type of domain maps. A domain map maps each representative (semantic
      value, of type [X.r]) to its associated domain.*)

  val pp : t Fmt.t
  (** Pretty-printer for domain maps. *)

  val empty : t
  (** The empty domain map. *)

  type elt
  (** The type of domains contained in the map. Each domain of type [elt]
      applies to a single semantic value. *)

  exception Inconsistent of Explanation.t
  (** Exception raised by [update], [subst] and [structural_propagation] when
      an inconsistency is detected. *)

  val add : X.r -> t -> t
  (** [add r t] adds a domain for [r] in the domain map. If [r] does not
      already have an associated domain, a fresh domain will be created for
      [r]. *)

  val get : X.r -> t -> elt
  (** [get r t] returns the domain currently associated with [r] in [t]. *)

  val update : X.r -> elt -> t -> t
  (** [update r d t] intersects the domain of [r] in [t] with the domain [d].

      {b Soundness}: The domain [d] must already include the justification
      that it applies to [r].

      @raise Inconsistent if this causes the domain associated with [r] to
      become empty. *)

  val fold_leaves : (X.r -> elt -> 'a -> 'a) -> t -> 'a -> 'a
  (** [fold f t acc] folds [f] over all the domains in [t] that are associated
      with leaves. *)

  val subst : ex:Explanation.t -> X.r -> X.r -> t -> t
  (** [subst ~ex p v d] replaces all the instances of [p] with [v] in all
      domains, merging the corresponding domains as appropriate.

      The explanation [ex] justifies the equality [p = v].

      @raise Inconsistent if this causes any domain in [d] to become empty. *)

  val choose_changed : t -> X.r * t
  (** [choose_changed d] returns a pair [r, d'] such that:

      - The domain associated with [r] has changed since the last time
        [choose_changed] was called.
      - [r] has (by definition) not changed in [d']

      Moreover, prior to returning [r], structural propagation is
      automatically performed.

      More precisely, if [r] is a leaf, the domain of [r] is propagated to any
      semantic value that contains [r] as a leaf according to the structure of
      that semantic value (using [Domain.map_leaves]); if [r] is not a leaf,
      its domain is propagated to any of the leaves it contains.

      We only perform *forward* structural propagation: if structural
      propagation causes a domain of a leaf or parent to be changed, then we
      will perform structural propagation for that leaf or parent once it
      itself is selected by [choose_changed].

      @raise Inconsistent if an inconsistency if detected during structural
      propagation. *)
end

module Domains_make(Domain : Domain) : Domains with type elt = Domain.t =
struct
  type elt = Domain.t

  exception Inconsistent = Domain.Inconsistent

  type t = {
    domains : Domain.t MX.t ;
    (** Map from tracked representatives to their domain *)

    changed : SX.t ;
    (** Representatives whose domain has changed since the last flush *)

    leaves_map : SX.t MX.t ;
    (** Map from leaves to the *tracked* representatives that contains them *)
  }

  let pp ppf t =
    Fmt.(iter_bindings ~sep:semi MX.iter
           (box @@ pair ~sep:(any " ->@ ") X.print Domain.pp)
         |> braces
        )
      ppf t.domains

  let empty =
    { domains = MX.empty ; changed = SX.empty ; leaves_map = MX.empty }

  let r_add r leaves_map =
    List.fold_left (fun leaves_map leaf ->
        MX.update leaf (function
            | Some parents -> Some (SX.add r parents)
            | None -> Some (SX.singleton r)
          ) leaves_map
      ) leaves_map (X.leaves r)

  let create_domain r =
    Domain.map_leaves (fun r () ->
        Domain.unknown (X.type_info r)
      ) r ()

  let add r t =
    match MX.find r t.domains with
    | _ -> t
    | exception Not_found ->
      (* Note: we do not need to mark [r] as needing propagation, because no
          constraints applied to it yet. Any constraint that apply to [r] will
          already be marked as pending due to being newly added. *)
      let d = create_domain r in
      let domains = MX.add r d t.domains in
      let leaves_map = r_add r t.leaves_map in
      { t with domains; leaves_map }

  let r_remove r leaves_map =
    List.fold_left (fun leaves_map leaf ->
        MX.update leaf (function
            | Some parents ->
              let parents = SX.remove r parents in
              if SX.is_empty parents then None else Some parents
            | None -> None
          ) leaves_map
      ) leaves_map (X.leaves r)

  let remove r t =
    let changed = SX.remove r t.changed in
    let domains = MX.remove r t.domains in
    let leaves_map = r_remove r t.leaves_map in
    { changed; domains; leaves_map }

  let get r t =
    (* We need to catch [Not_found] because of fresh terms that can be added
        by the solver and for which we don't call [add]. Note that in this
        case, only structural constraints can apply to [r]. *)
    try MX.find r t.domains with Not_found -> create_domain r

  let update r d t =
    match MX.find r t.domains with
    | od ->
      (* Both domains are already valid for [r], we can intersect them
          without additional justifications. *)
      let d = Domain.intersect ~ex:Explanation.empty od d in
      if Domain.equal od d then
        t
      else
        let domains = MX.add r d t.domains in
        let changed = SX.add r t.changed in
        { t with domains; changed }
    | exception Not_found ->
      (* We need to catch [Not_found] because of fresh terms that can be added
          by the solver and for which we don't call [add]. *)
      let d = Domain.intersect ~ex:Explanation.empty d (create_domain r) in
      let domains = MX.add r d t.domains in
      let changed = SX.add r t.changed in
      let leaves_map = r_add r t.leaves_map in
      { domains; changed; leaves_map }

  let fold_leaves f t acc =
    MX.fold (fun r _ acc ->
        f r (get r t) acc
      ) t.leaves_map acc

  let subst ~ex rr nrr t =
    match MX.find rr t.leaves_map with
    | parents ->
      SX.fold (fun r t ->
          let d =
            try MX.find r t.domains
            with Not_found ->
              (* [r] was in the [leaves_map] to it must have a domain *)
              assert false
          in
          let changed = SX.mem r t.changed in
          let t = remove r t in
          let nr = X.subst rr nrr r in
          match MX.find nr t.domains with
          | nd ->
            (* If there is an existing domain for [nr], there might be
                constraints applying to [nr] prior to the substitution, and the
                constraints that used to apply to [r] will also apply to [nr]
                after the substitution.

                We need to notify changed to either of these constraints, so we
                must notify if the domain is different from *either* the old
                domain of [r] or the old domain of [nr]. *)
            let nnd = Domain.intersect ~ex d nd in
            let nr_changed = not (Domain.equal nnd nd) in
            let r_changed = not (Domain.equal nnd d) in
            let domains =
              if nr_changed then MX.add nr nnd t.domains else t.domains
            in
            let changed = changed || r_changed || nr_changed in
            let changed =
              if changed then SX.add nr t.changed else t.changed
            in
            { t with domains; changed }
          | exception Not_found ->
            (* If there is no existing domain for [nr], there were no
                constraints applying to [nr] prior to the substitution.

                The only constraints that need to be notified are those that
                were applying to [r], and they only need to be notified if the
                new domain is different from the old domain of [r]. *)
            let nd = Domain.intersect ~ex d (create_domain nr) in
            let r_changed = not (Domain.equal nd d) in
            let domains = MX.add nr nd t.domains in
            let leaves_map = r_add nr t.leaves_map in
            let changed = changed || r_changed in
            let changed =
              if changed then SX.add nr t.changed else t.changed
            in
            { domains; changed; leaves_map }
        ) parents t
    | exception Not_found ->
      (* We are not tracking any semantic value that have [r] as a leaf, so we
          have nothing to do. *)
      t

  let structural_propagation r t =
    if X.is_a_leaf r then
      match MX.find r t.leaves_map with
      | parents ->
        SX.fold (fun parent t ->
            if X.is_a_leaf parent then (
              assert (X.equal r parent);
              t
            ) else
              update parent (Domain.map_leaves get parent t) t
          ) parents t
      | exception Not_found -> t
    else
      Domain.fold_leaves update r (get r t) t

  let choose_changed t =
    let r = SX.choose t.changed in
    let t = { t with changed = SX.remove r t.changed } in
    r, structural_propagation r t
end

module type Constraint = sig
  type t
  (** The type of constraints.

      Constraints apply to semantic values of type [X.r] as arguments. *)

  val pp : t Fmt.t
  (** Pretty-printer for constraints. *)

  val compare : t -> t -> int
  (** Comparison function for constraints. The comparison function is
      arbitrary and has no semantic meaning. You should not depend on any of
      its properties, other than it defines an (arbitrary) total order on
      constraint representations. *)

  val fold_args : (X.r -> 'a -> 'a) -> t -> 'a -> 'a
  (** [fold_args f c acc] folds function [f] over the arguments of constraint
      [c].

      During propagation, the constraint {b MUST} only look at (and update)
      the domains associated of its arguments; it is not allowed to look at
      the domains of other semantic values. This allows efficient updates of
      the pending constraints. *)

  val subst : X.r -> X.r -> t -> t
  (** [subst p v cs] replaces all the instances of [p] with [v] in the
      constraint.

      Substitution can perform constraint simplification. *)
end

type 'a explained = { value : 'a ; explanation : Explanation.t }

let explained ~ex value = { value ; explanation = ex }

module Constraints_make(Constraint : Constraint) : sig
  type t
  (** The type of constraint sets. A constraint set records a set of
      constraints that applies to semantic values, and remembers the relation
      between constraints and semantic values.

      The constraints associated with specific semantic values can be notified
      (see [notify]), which is used to only propagate constraints involving
      semantic values whose domain has changed.

      The constraints that have been notified are called "pending
      constraints", and the set thereof is the "pending set". These are
      constraints that need to be propagated, and can be recovered using
      [next_pending]. *)

  val pp : t Fmt.t
  (** Pretty-printer for constraint sets. *)

  val empty : t
  (** The empty constraint set. *)

  val add : ex:Explanation.t -> Constraint.t -> t -> t
  (** [add ~ex c t] adds the constraint [c] to the set [t].

      The explanation [ex] justifies that the constraint [c] holds. If the same
       constraint is added multiple times with different explanations, only one
       of the explanations for the constraint will be kept. *)

  val subst : ex:Explanation.t -> X.r -> X.r -> t -> t
  (** [subst ~ex p v t] replaces all instances of [p] with [v] in the
      constraints.

      The explanation [ex] justifies the equality [p = v]. *)

  val notify : X.r -> t -> t
  (** [notify r t] marks all constraints involving [r] (i.e. all constraints
      that have [r] as one of their arguments) as pending.

      This function should be used when the domain of [r] is updated, if
      domains are tracked for all representatives. *)

  val notify_leaf : X.r -> t -> t
  (** [notify_leaf r t] marks all constraints that have [r] as a leaf (i.e.
      all constraints that have at least one argument [a] such that [r] is in
      [X.leaves a]) as pending.

      This function should be used when the domain of [r] is updated, if
      domains are tracked for leaves only. *)

  val fold_args : (X.r -> 'a -> 'a) -> t -> 'a -> 'a
  (** [fold_args f t acc] folds [f] over all the term representatives that are
      arguments of at least one constraint. *)

  val next_pending : t -> Constraint.t explained * t
  (** [next_pending t] returns a pair [c, t'] where [c] was pending in [t] and
      [t'] is identical to [t], except that [c] is no longer a pending
      constraint.

      @raise Not_found if there are no pending constraints. *)
end = struct
  module CS = Set.Make(struct
      type t = Constraint.t explained

      let compare a b = Constraint.compare a.value b.value
    end)

  type t = {
    args_map : CS.t MX.t ;
    (** Mapping from semantic values to constraints involving them *)

    leaves_map : CS.t MX.t ;
    (** Mapping from semantic values to constraints they are a leaf of *)

    active : CS.t ;
    (** Set of all currently active constraints, i.e. constraints that must
        hold in a model and will be propagated.  *)

    pending : CS.t ;
    (** Set of active constraints that have not yet been propagated *)
  }

  let pp ppf { active; _ } =
    Fmt.(
      braces @@ hvbox @@
      iter ~sep:semi CS.iter @@
      using (fun { value; _ } -> value) @@
      box ~indent:2 @@ braces @@
      Constraint.pp
    ) ppf active

  let empty =
    { args_map = MX.empty
    ; leaves_map = MX.empty
    ; active = CS.empty
    ; pending = CS.empty }

  let cs_add c r cs_map =
    MX.update r (function
        | Some cs -> Some (CS.add c cs)
        | None -> Some (CS.singleton c)
      ) cs_map

  let fold_leaves f c acc =
    Constraint.fold_args (fun r acc ->
        List.fold_left (fun acc r -> f r acc) acc (X.leaves r)
      ) c acc

  let add ~ex c t =
    let c = explained ~ex c in
    (* Note: use [CS.find] here, not [CS.mem], to ensure we use the same
       explanation for [c] in the [pending] and [active] sets. *)
    if CS.mem c t.active then t else
      let active = CS.add c t.active in
      let args_map =
        Constraint.fold_args (cs_add c) c.value t.args_map
      in
      let leaves_map = fold_leaves (cs_add c) c.value t.leaves_map in
      let pending = CS.add c t.pending in
      { active; args_map; leaves_map; pending }

  let cs_remove c r cs_map =
    MX.update r (function
        | Some cs ->
          let cs = CS.remove c cs in
          if CS.is_empty cs then None else Some cs
        | None -> None
      ) cs_map

  let remove c t =
    let active = CS.remove c t.active in
    let args_map =
      Constraint.fold_args (cs_remove c) c.value t.args_map
    in
    let leaves_map = fold_leaves (cs_remove c) c.value t.leaves_map in
    let pending = CS.remove c t.pending in
    { active; args_map; leaves_map; pending }

  let subst ~ex rr nrr t =
    match MX.find rr t.leaves_map with
    | cs ->
      CS.fold (fun c t ->
          let t = remove c t  in
          let ex = Explanation.union ex c.explanation in
          add ~ex (Constraint.subst rr nrr c.value) t
        ) cs t
    | exception Not_found -> t

  let notify r t =
    match MX.find r t.args_map with
    | cs ->
      CS.fold (fun c t -> { t with pending = CS.add c t.pending }) cs t
    | exception Not_found -> t

  let notify_leaf r t =
    match MX.find r t.leaves_map with
    | cs ->
      CS.fold (fun c t -> { t with pending = CS.add c t.pending }) cs t
    | exception Not_found -> t

  let fold_args f c acc =
    MX.fold (fun r _ acc ->
        f r acc
      ) c.args_map acc

  let next_pending t =
    let c = CS.choose t.pending in
    c, { t with pending = CS.remove c t.pending }
end
