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

module Congruence : sig
  (** The [Congruence] module implements a simil-congruence closure algorithm on
      semantic values.

      It provides an interface to register some semantic values of interest, and
      for applying a callback when the representative of those registered values
      change.
  *)

  type t
  (** The type of congruences. *)

  val empty : t
  (** The empty congruence. *)

  val add : X.r -> t -> t
  (** [add r t] registers the semantic value [r] in the congruence. *)

  val remove : X.r -> t -> t
  (** [remove r t] unregisters the semantic value [r] from the congruence.

      Note that if substitutions have been applied to the congruence after a
      value has been added, those same substitutions must be applied to the
      semantic value prior to calling [remove], or [Invalid_argument] will be
      raised.

      @raise [Invalid_argument] if [r] is not a registered semantic value. *)

  val subst : X.r -> X.r -> t -> (X.r -> X.r -> 'a -> 'a) -> 'a -> t * 'a
  (** [subst p v t f x] performs a local congruence closure of the
      substitution [p -> v].

      More precisely, it will fold [f] over the pairs [(rr, nrr)] such that:
      - [rr] was registered in the congruence
      - [nrr] is [X.subst p v rr]

      For each such pair, [rr] is then unregistered from the congruence, and
      [nrr] is registered instead.

      [f] is intended to perform a substitution operation on the type ['a],
      merging the values associated with [rr] into the values associated with
      [nrr]. *)

  val fold_parents : (X.r -> 'a -> 'a) -> t -> X.r -> 'a -> 'a
  (** [fold_parents f t r acc] folds function [f] over all the registered terms
      whose current representative contains [r] as a leaf. *)
end = struct
  module SX = Shostak.SXH
  module MX = Shostak.MXH

  type t =
    { parents : SX.t MX.t
    (** Map from leaves to terms that contain them as a leaf.

        [p] is in [parents(x)] => [x] is in [leaves(p)] *)
    ; registered : SX.t
    (** The set of terms we care about. If [x] is in [registered],
        then [x] is also in [parents(y)] for each [y] in [leaves(x)]. *)
    }

  let empty = { parents = MX.empty ; registered = SX.empty }

  let fold_parents f { parents; _ } r acc =
    match MX.find r parents with
    | deps -> SX.fold f deps acc
    | exception Not_found -> acc

  let add r t =
    if SX.mem r t.registered then
      t
    else
      let parents =
        List.fold_left (fun parents leaf ->
            MX.update leaf (function
                | Some deps -> Some (SX.add r deps)
                | None -> Some (SX.singleton r)
              ) parents
          ) t.parents (X.leaves r)
      in
      { parents ; registered  = SX.add r t.registered }

  let remove r t =
    if SX.mem r t.registered then
      let parents =
        List.fold_left (fun parents leaf ->
            MX.update leaf (function
                | Some deps ->
                  let deps = SX.remove r deps in
                  if SX.is_empty deps then None else Some deps
                | None ->
                  (* [r] is in registered, and [leaf] is in [leaves(r)], so
                     [r] must be in [parents(leaf)]. *)
                  assert false
              ) parents
          ) t.parents (X.leaves r)
      in
      { parents ; registered = SX.remove r t.registered }
    else
      invalid_arg "Congruence.remove"

  let subst rr nrr cgr f t =
    match MX.find rr cgr.parents with
    | rr_deps ->
      let cgr = { cgr with parents = MX.remove rr cgr.parents } in
      SX.fold (fun r (cgr, t) ->
          let r' = X.subst rr nrr r in
          (* [r] contains [rr] as a leaf by definition *)
          assert (not (X.equal r r'));

          (* Update the other leaves *)
          let parents =
            List.fold_left (fun parents other_leaf ->
                if X.equal other_leaf rr then
                  parents
                else
                  MX.update other_leaf (function
                      | Some deps ->
                        let deps = SX.remove r deps in
                        if SX.is_empty deps then None else Some deps
                      | None -> assert false
                    ) parents
              ) cgr.parents (X.leaves r)
          in

          (* It is no longer here, but it could be added back later -- let's not
             skip it! *)
          let registered = SX.remove r cgr.registered in

          (* Add the new representative to the congruence if needed *)
          let cgr = add r' { parents ; registered } in

          (* Propagate the substitution *)
          cgr, f r r' t
        ) rr_deps (cgr, t)
    | exception Not_found -> cgr, t
end
