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
  List.rev_map (fun (sa, _, ex, orig) -> Sig_rel.LSem sa, ex, orig) eqs

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
    (* The `Subst` origin is used when `r1 -> r2` is added in the
        union-find. The `CS _` and `NCS _` origins are used for case splits. In
        both cases, we want to be propagating the constant.

        Note that equalities of `Subst` origins are oriented: for `Subst`, `r2`
        is the (new) normal form for `r1.

        Usually, this would be true of case-split equalities as well (of the
        form `r = v` where `v` is the chosen value), but this is not true for
        the case splits that come from the arrays theory (in fact, the array
        theory produces *dis*equality case splits, and the equality ends up in
        the `NCS` instead), so we don't try to be smart and pay the (small)
        performance cost.

        `Other` cases should (I believe...) be subsumed by `Subst`. The original
        code in the arithmetic theory that this is lifted from from was only
        considering `Subst`, and was allowing possibly incorrect models.

        Note that we need to handle `CS` and `NCS` here to produce correct
        models, but also this can cause eager enumeration, so by excess of
        caution we only use it when model generation has been requested. It is
        unknown whether eager enumeration would be an actual problem in
        practice. *)
    match orig with
    | Th_util.Subst when X.is_constant r2 -> update env uf r1 eqs
    | CS _ | NCS _ when Options.get_interpretation () ->
      update env uf r2 (update env uf r1 eqs)
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
