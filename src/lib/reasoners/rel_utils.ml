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
module MXH = Shostak.MXH
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
    used_by : Expr.Set.t OMap.t MXH.t ;
  }

  let create dispatch = { dispatch; used_by = MXH.empty }

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
                  MXH.update (Uf.make uf x) (fun sm ->
                      let sm = Option.value ~default:OMap.empty sm in
                      Option.some @@
                      OMap.update f (fun se ->
                          let se = Option.value ~default:Expr.Set.empty se in
                          Some (Expr.Set.add t se)) sm) used_by) used_by xs
            in { env with used_by }, []
      )
    | _ -> env, []

  let update { dispatch; used_by } uf r1 eqs =
    match MXH.find r1 used_by with
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

module type Constraint = sig
  type t
  (** The type of constraints.

      Constraints are associated with a justification as to why they are
      currently valid. The justification is only used to update domains,
      identical constraints with different justifications will otherwise behave
      identically (and, notably, will compare equal).

      Constraints contains semantic values / term representatives of type
      [X.r]. We maintain the invariant that the semantic values used inside the
      constraints are *class representatives* i.e. normal forms wrt the `Uf`
      module, i.e. constraints have a normalized representation. Use `subst` to
      ensure normalization. *)

  val pp : t Fmt.t
  (** Pretty-printer for constraints. *)

  val compare : t -> t -> int
  (** Comparison function for constraints.

      Constraints typically include explanations, which should not be included
      in the comparison function: code working with constraints expects
      constraints with identical representations but different explanations to
      compare equal.

      {b Note}: The comparison function is arbitrary and has no semantic
      meaning. You should not depend on any of its properties, other than it
      defines an (arbitrary) total order on constraint representations. *)

  val subst : Explanation.t -> X.r -> X.r -> t -> t
  (** [subst ex p v cs] replaces all the instances of [p] with [v] in the
      constraint.

      Use this to ensure that the representation is always normalized.

      The explanation [ex] justifies the equality [p = v]. *)

  val fold_leaves : (X.r -> 'a -> 'a) -> t -> 'a -> 'a

  type domain
  (** The type of domains.

      This is typically a mapping from variables to their own domain, but no
      expectations is made upon the actual structure of that type. *)

  val propagate : t -> domain -> domain
  (** [propagate c dom] propagates the constraints [c] in [d] and returns the
      new domain. *)

end

module Constraints_Make(Constraint : Constraint) : sig
  type t
  (** The type of constraint sets. A constraint sets records a set of
      constraints that applies to semantic values, and remembers which
      constraints are associated with each semantic values.

      It is used to only propagate constraints involving semantic values whose
      associated domain has changed.

      The constraint sets are expected to keep track of *class representatives*,
      i.e.  normal forms wrt the `Uf` module, in which case we say the
      constraint set is *normalized*. Use `subst` to ensure normalization. *)

  val pp : t Fmt.t
  (** Pretty-printer for constraint sets. *)

  val empty : t
  (** Returns an empty constraint set. *)

  val subst : Explanation.t -> X.r -> X.r -> t -> t
  (** [subst ex p v cs] replaces all the instances of [p] with [v] in the
      constraints.

      Use this to ensure that the representation is always normalized.

      The explanation [ex] justifies the equality [p = v]. *)

  val add : t -> Constraint.t -> t
  (** [add c cs] adds the constraint [c] to [cs]. *)

  val propagate_fresh :  t -> Constraint.domain -> t * Constraint.domain
  (** [propagate_fresh cs acc] propagates the fresh constraints and returns the
      new domain, as well as a copy of the constraint set with no fresh
      constraints.

      Fresh constraints are constraints that were never propagated yet. *)

  val fold_r : (X.r -> 'a -> 'a) -> t -> 'a -> 'a
  (** [fold_r f cs acc] folds [f] over any representative [r] that is currently
      associated with a constraint (i.e. at least one constraint currently
      applies to [r]). *)

  val propagate : t -> X.r -> Constraint.domain -> Constraint.domain
  (** [propagate cs r dom] propagates the constraints associated with [r] in the
      constraint set [cs] and returns the new domain map after propagation. *)
end = struct
  module IM = Util.MI
  module MX = Shostak.MXH

  module CS = Set.Make(Constraint)

  type t = {
    cs_set : CS.t ;
    (*** All the constraints currently active *)
    cs_map : CS.t MX.t ;
    (*** Mapping from semantic values to the constraints that involves them *)
    fresh : CS.t ;
    (*** Fresh constraints that have never been propagated *)
  }

  let pp ppf { cs_set; cs_map = _ ; fresh = _ } =
    Fmt.(
      braces @@ hvbox @@
      iter ~sep:semi CS.iter @@
      box ~indent:2 @@ braces @@
      Constraint.pp
    ) ppf cs_set

  let empty =
    { cs_set = CS.empty
    ; cs_map = MX.empty
    ; fresh = CS.empty }

  let cs_add cs r cs_map =
    MX.update r (function
        | Some css -> Some (CS.add cs css)
        | None -> Some (CS.singleton cs)
      ) cs_map

  let cs_remove cs r cs_map =
    MX.update r (function
        | Some css ->
          let css = CS.remove cs css in
          if CS.is_empty css then None else Some css
        | None ->
          (* Can happen if the same argument is repeated *)
          None
      ) cs_map

  let subst ex rr nrr bcs =
    match MX.find rr bcs.cs_map with
    | ids ->
      let cs_map, cs_set, fresh =
        CS.fold (fun cs (cs_map, cs_set, fresh) ->
            let fresh = CS.remove cs fresh in
            let cs_set = CS.remove cs cs_set in
            let cs_map = Constraint.fold_leaves (cs_remove cs) cs cs_map in
            let cs' = Constraint.subst ex rr nrr cs in
            if CS.mem cs' cs_set then
              cs_map, cs_set, fresh
            else
              let cs_set = CS.add cs' cs_set in
              let cs_map = Constraint.fold_leaves (cs_add cs') cs' cs_map in
              (cs_map, cs_set, CS.add cs' fresh)
          ) ids (bcs.cs_map, bcs.cs_set, bcs.fresh)
      in
      assert (not (MX.mem rr cs_map));
      { cs_set ; cs_map ; fresh }
    | exception Not_found -> bcs

  let add bcs c =
    if CS.mem c bcs.cs_set then
      bcs
    else
      let cs_set = CS.add c bcs.cs_set in
      let cs_map = Constraint.fold_leaves (cs_add c) c bcs.cs_map in
      let fresh = CS.add c bcs.fresh in
      { cs_set ; cs_map ; fresh }

  let fold_r f bcs acc =
    MX.fold (fun r _ acc -> f r acc) bcs.cs_map acc

  let propagate bcs r dom =
    match MX.find r bcs.cs_map with
    | cs -> CS.fold Constraint.propagate cs dom
    | exception Not_found -> dom

  let propagate_fresh bcs dom =
    let dom = CS.fold Constraint.propagate bcs.fresh dom in
    { bcs with fresh = CS.empty }, dom
end
