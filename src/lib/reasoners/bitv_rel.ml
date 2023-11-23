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
(*     ---------------------------------------------------------------    *)
(*                                                                        *)
(*     The Alt-Ergo theorem prover                                        *)
(*                                                                        *)
(*     Sylvain Conchon, Evelyne Contejean, Francois Bobot                 *)
(*     Mohamed Iguernelala, Stephane Lescuyer, Alain Mebsout              *)
(*                                                                        *)
(*     CNRS - INRIA - Universite Paris Sud                                *)
(*                                                                        *)
(*     Until 2013, some parts of this code were released under            *)
(*     the Apache Software License version 2.0.                           *)
(*                                                                        *)
(*     ---------------------------------------------------------------    *)
(*                                                                        *)
(*     More details can be found in the directory licenses/               *)
(*                                                                        *)
(**************************************************************************)

module E = Expr
module Ex = Explanation
module Sy = Symbols
module X = Shostak.Combine
module L = Xliteral
module Congruence = Rel_utils.Congruence

(* Currently we only compute, but in the future we may want to perform the same
   simplifications as in [Bitv.make]. We currently don't, because we don't
   really have a way to share code that uses polynome between the theory and the
   relations without touching the Shostak [module rec].

   Note that if we *do* want to compute here, the check for [X.is_constant] in
   [Rel_utils.update] needs to be removed, which may have (small) performance
   implications. *)
let bv2nat _op bv =
  match Bitv.to_Z_opt bv with
  | Some n -> Some (Shostak.Polynome.create [] (Q.of_bigint n) Tint)
  | None -> None

(* [int2bv] is in the bitvector theory rather than the arithmetic theory because
   we treat the arithmetic as more "primitive" than bit-vectors. *)
let int2bv op p =
  match op, Shostak.Polynome.is_const p with
  | Symbols.Int2BV n, Some q ->
    assert (Z.equal (Q.den q) Z.one);
    let m = Q.to_bigint q in
    Some (Bitv.int2bv_const n m)
  | Int2BV _, None -> None
  | _ -> assert false

let delay1 = Rel_utils.delay1

let dispatch = function
  | Symbols.BV2Nat ->
    Some (delay1 Shostak.Bitv.embed Shostak.Arith.is_mine bv2nat)
  | Int2BV _ ->
    Some (delay1 Shostak.Arith.embed Shostak.Bitv.is_mine int2bv)
  | _ -> None

let is_bv_ty = function
  | Ty.Tbitv _ -> true
  | _ -> false

let is_bv_r r = is_bv_ty @@ X.type_info r

module SX = Shostak.SXH
module MX = Shostak.MXH

module Domains : sig
  type t
  (** The type of domain maps. A domain map maps each representatives (semantic
      values, of type [X.r]) to their associated domains.

      The keys of the domain maps are expected to be current *class
      representatives*, i.e.  normal forms wrt the `Uf` module, in which case we
      say the domain map is *normalized*. Use `subst` to ensure that domain maps
      stay normalized. *)

  val pp : t Fmt.t
  (** Pretty-printer for domain maps. *)

  val empty : t
  (** Returns an empty domain map. *)

  val update : Ex.t -> X.r -> t -> Bitlist.t -> t
  (** [update ex r d bl] intersects the domain of [r] with bitlist [bl].

      The explanation [ex] justifies that [bl] applies to [r]. *)

  val get : X.r -> t -> Bitlist.t
  (** [get r d] returns the bitlist currently associated with [r] in [d].

      @raise Not_found if there is no bitlist associated with [r] in [d]. *)

  val subst : Ex.t -> X.r -> X.r -> t -> t
  (** [subst ex p v d] replaces all the instances of [p] with [v] in any domain,
      and merges the corresponding bitlists.

      Use this to ensure that the representation is always normalized.

      [v] must have an existing associated domain (possibly unconstrained)
      before calling [subst]. Call [update] beforehand.

      The explanation [ex] justifies the equality [p = v]. *)

  val choose_changed : t -> X.r * t
  (** [choose_changed d] returns a pair [r, d'] such that:

      - The domain associated with [r] has changed since the last time
         [choose_changed] was called,
      - [r] has (by definition) not changed in [d'] *)

  val fold : (X.r -> Bitlist.t -> 'a -> 'a) -> t -> 'a -> 'a
  (** [fold f d acc] folds [f] over all the domains associated with variables *)
end = struct
  type t =
    { bitlists : Bitlist.t MX.t
    (** Mapping from semantic values to their bitlist domain. *)
    ; changed : SX.t
    (** Elements whose domain has changed since last propagation. *)
    }

  let pp ppf t =
    Fmt.(iter_bindings ~sep:semi MX.iter
           (box @@ pair ~sep:(any " ->@ ") X.print Bitlist.pp)
         |> braces
        )
      ppf t.bitlists
  let empty = { bitlists = MX.empty ; changed = SX.empty }

  let update ex r t bl =
    let changed = ref false in
    let bitlists =
      MX.update r (function
          | Some bl' as o ->
            let bl'' = Bitlist.intersect bl bl' ex in
            (* Keep simpler explanations, and don't loop adding the domain to
               the changed set infinitely. *)
            if Bitlist.equal bl' bl'' then
              o
            else (
              if Options.get_debug_bitv () then
                Printer.print_dbg
                  ~module_name:"Bitv_rel" ~function_name:"Domain.update"
                  "domain shrunk for %a: %a -> %a"
                  X.print r Bitlist.pp bl' Bitlist.pp bl'';
              changed := true;
              Some bl''
            )
          | None ->
            changed := true;
            Some (Bitlist.add_explanation bl ex)
        ) t.bitlists
    in
    let changed = if !changed then SX.add r t.changed else t.changed in
    { changed; bitlists }

  let get r t =
    try MX.find r t.bitlists with
    | Not_found ->
      match X.type_info r with
      | Tbitv n -> Bitlist.unknown n Explanation.empty
      | _ -> assert false

  let subst ex rr nrr t =
    match MX.find rr t.bitlists with
    | bl ->
      let has_changed = ref (SX.mem rr t.changed) in
      let bitlists =
        MX.update nrr (function
            | Some bl' as o ->
              let bl'' = Bitlist.intersect bl bl' ex in
              (* Keep simpler explanations, and don't loop adding the domain to
                 the changed set infinitely. *)
              if Bitlist.equal bl' bl'' then
                o
              else (
                has_changed := true;
                if Options.get_debug_bitv () then
                  Printer.print_dbg
                    ~module_name:"Bitv_rel" ~function_name:"Domain.subst"
                    "domain shrunk for %a: %a -> %a"
                    X.print nrr Bitlist.pp bl' Bitlist.pp bl'';
                Some (Bitlist.intersect bl bl' ex)
              )
            | None ->
              (* We require that [nrr] has a domain before calling [subst]. *)
              Printer.print_err
                "Bitv_rel: substituting %a -> %a without domain"
                X.print rr X.print nrr;
              assert false
          ) @@ MX.remove rr t.bitlists
      in
      let changed = SX.remove rr t.changed in
      let changed = if !has_changed then SX.add nrr changed else changed in
      { changed ; bitlists }
    | exception Not_found -> t

  let choose_changed t =
    let r = SX.choose t.changed in
    r, { t with changed = SX.remove r t.changed }

  let fold f t = MX.fold f t.bitlists
end

module Constraint : sig
  type repr =
    | Band of X.r * X.r * X.r
    (** [Band (x, y, z)] represents [x = y & z] *)
    | Bor of X.r * X.r * X.r
    (** [Bor (x, y, z)] represents [x = y | z] *)
    | Bxor of SX.t
    (** [Bxor {x1, ..., xn}] represents [x1 ^ ... ^ xn = 0] *)
    | Bnot of X.r * X.r
    (** [Bnot (x, y)] represents [x = not y] *)

  type tagged_repr

  val hcons : repr -> tagged_repr
  (** Internalize the constraint representation.

      This uses hash-consing and some simple normalization to de-duplicate
      constraints. *)

  val tag : tagged_repr -> int
  (** Returns the unique tag associated with the tagged repr. *)

  type t = { repr : tagged_repr ; ex : Ex.t }
  (** The type of bit-vector constraints.

      Bit-vector constraints contains semantic values / term representatives of
      type [X.r]. We maintain the invariant that the semantic values used inside
      the constraints are *class representatives* i.e. normal forms wrt the `Uf`
      module, i.e. constraints have a normalized representation. Use `subst` to
      ensure normalization. *)

  val pp : t Fmt.t
  (** Pretty-printer for constraints. *)

  val subst : Ex.t -> X.r -> X.r -> t -> t
  (** [subst ex p v cs] replaces all the instaces of [p] with [v] in the
      constraint.

      Use this to ensure that the representation is always normalized.

      The explanation [ex] justifies the equality [p = v]. *)

  val fold_deps : (X.r -> 'a -> 'a) -> t -> 'a -> 'a
  (** [fold_deps f c acc] accumulates [f] over the arguments of [c]. *)

  val propagate : t -> Domains.t -> Domains.t
  (** [propagate c dom] propagates the constraints [c] in [d] and returns the
      new domains. *)
end = struct
  type repr =
    | Band of X.r * X.r * X.r
    | Bor of X.r * X.r * X.r
    | Bxor of SX.t
    | Bnot of X.r * X.r

  let normalize_repr = function
    | Band (x, y, z) when X.hash_cmp y z > 0 -> Band (x, z, y)
    | Bor (x, y, z) when X.hash_cmp y z > 0 -> Bor (x, z, y)
    | repr -> repr

  let equal_repr r1 r2 =
    match r1, r2 with
    | Band (x1, y1, z1), Band (x2, y2, z2)
    | Bor (x1, y1, z1), Bor (x2, y2, z2) ->
      X.equal x1 x2 && X.equal y1 y2 && X.equal z1 z2
    | Bxor xs1, Bxor xs2 -> SX.equal xs1 xs2
    | Bnot (x1, y1), Bnot (x2, y2) ->
      (X.equal x1 x2 && X.equal y1 y2)
    | Band _, _
    | Bor _, _
    | Bxor _, _
    | Bnot _, _ -> false

  let hash_repr = function
    | Band (x, y, z) -> Hashtbl.hash (0, X.hash x, X.hash y, X.hash z)
    | Bor (x, y, z) -> Hashtbl.hash (1, X.hash x, X.hash y, X.hash z)
    | Bxor xs ->
      Hashtbl.hash (2, SX.fold (fun r acc -> X.hash r :: acc) xs [])
    | Bnot (x, y) -> Hashtbl.hash (2, X.hash x, X.hash y)

  type tagged_repr = { repr : repr ; mutable tag : int }

  module W = Weak.Make(struct
      type t = tagged_repr

      let equal { repr = lhs; _ } { repr = rhs; _ } = equal_repr lhs rhs

      let hash { repr; _ } = hash_repr repr
    end)

  let hcons =
    let cnt = ref 0 in
    let tbl = W.create 17 in
    fun repr ->
      let repr = normalize_repr repr in
      let tagged = W.merge tbl { repr ; tag = -1 } in
      if tagged.tag = -1 then (
        tagged.tag <- !cnt;
        incr cnt
      );
      tagged

  let tag { tag; _ } = tag

  let pp_repr ppf = function
    | Band (x, y, z) ->
      Format.fprintf ppf "%a & %a = %a" X.print y X.print z X.print x
    | Bor (x, y, z) ->
      Format.fprintf ppf "%a | %a = %a" X.print y X.print z X.print x
    | Bxor xs ->
      Fmt.(iter ~sep:(any " ^@ ") SX.iter X.print |> box) ppf xs;
      Fmt.pf ppf " = 0"
    | Bnot (x, y) ->
      Format.fprintf ppf "%a = ~%a" X.print x X.print y

  (* TODO: for bitwise constraints (eg Band, Bor, Bxor)
      on initialisation and also after substitution
      we should split the domain
  *)

  let subst_repr rr nrr = function
    | Band (x, y, z) ->
      let x = if X.equal x rr then nrr else x
      and y = if X.equal y rr then nrr else y
      and z = if X.equal z rr then nrr else z in
      Band (x, y, z)
    | Bor (x, y, z) ->
      let x = if X.equal x rr then nrr else x
      and y = if X.equal y rr then nrr else y
      and z = if X.equal z rr then nrr else z in
      Bor (x, y, z)
    | Bxor xs ->
      Bxor (
        SX.fold (fun r xs ->
            let r = if X.equal r rr then nrr else r in
            if SX.mem r xs then SX.remove r xs else SX.add r xs
          ) xs SX.empty
      )
    | Bnot (x, y) ->
      let x = if X.equal x rr then nrr else x
      and y = if X.equal y rr then nrr else y in
      Bnot (x, y)

  (* The explanation justifies why the constraint holds. *)
  type t = { repr : tagged_repr ; ex : Ex.t }

  let pp ppf { repr; _ } = pp_repr ppf repr.repr

  let subst ex rr nrr c =
    { repr = hcons @@ subst_repr rr nrr c.repr.repr ; ex = Ex.union ex c.ex }

  let fold_deps f { repr; _ } acc =
    match repr.repr with
    | Band (x, y, z) | Bor (x, y, z) ->
      let acc = f x acc in
      let acc = f y acc in
      let acc = f z acc in
      acc
    | Bxor xs -> SX.fold f xs acc
    | Bnot (x, y) ->
      let acc = f x acc in
      let acc = f y acc in
      acc

  let propagate { repr; ex } dom =
    match repr.repr with
    | Band (x, y, z) ->
      let dx = Domains.get x dom
      and dy = Domains.get y dom
      and dz = Domains.get z dom
      in
      let dom = Domains.update ex x dom @@ Bitlist.logand dy dz in
      (* Reverse propagation for y: if [x = y & z] then:
         - Any [1] in [x] must be a [1] in [y]
         - Any [0] in [x] that is also a [1] in [z] must be a [0] in [y]
      *)
      let dom =
        Domains.update ex y dom @@
        Bitlist.(intersect (ones dx) (logor (zeroes dx) (lognot (ones dz))) ex)
      in
      let dom =
        Domains.update ex z dom @@
        Bitlist.(intersect (ones dx) (logor (zeroes dx) (lognot (ones dy))) ex)
      in
      dom
    | Bor (x, y, z) ->
      let dx = Domains.get x dom
      and dy = Domains.get y dom
      and dz = Domains.get z dom
      in
      let dom = Domains.update ex x dom @@ Bitlist.logor dy dz in
      (* Reverse propagation for y: if [x = y | z] then:
         - Any [0] in [x] must be a [0] in [y]
         - Any [1] in [x] that is also a [0] in [z] must be a [1] in [y]
      *)
      let dom =
        Domains.update ex y dom @@ Bitlist.(
            intersect (zeroes dx) (logand (ones dx) (lognot (zeroes dz))) ex
          )
      in
      let dom =
        Domains.update ex z dom @@ Bitlist.(
            intersect (zeroes dx) (logand (ones dx) (lognot (zeroes dy))) ex
          )
      in
      dom
    | Bxor xs ->
      SX.fold (fun x dom ->
          let dx = Domains.get x dom in
          let dx' =
            SX.fold (fun y acc ->
                if X.equal x y then
                  acc
                else
                  Bitlist.logxor (Domains.get y dom) acc
              ) xs (Bitlist.exact (Bitlist.width dx) Z.zero Ex.empty)
          in
          Domains.update ex x dom dx'
        ) xs dom
    | Bnot (x, y) ->
      let dx = Domains.get x dom and dy = Domains.get y dom in
      let dom = Domains.update ex x dom @@ Bitlist.lognot dy in
      let dom = Domains.update ex y dom @@ Bitlist.lognot dx in
      dom
end

module Constraints : sig
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

  val subst : Ex.t -> X.r -> X.r -> t -> t
  (** [subst ex p v cs] replaces all the instances of [p] with [v] in the
      constraints.

      Use this to ensure that the representation is always normalized.

      The explanation [ex] justifies the equality [p = v]. *)

  val add : t -> Constraint.t -> t
  (** [add c cs] adds the constraint [c] to [cs]. *)

  val fold_fresh : (Constraint.t -> 'a -> 'a) -> t -> 'a -> t * 'a
  (** [fold_fresh f cs acc] folds [f] over the fresh constraints in [cs].

      Fresh constraints are constraints that were never propagated yet. *)

  val propagate : t -> X.r -> Domains.t -> Domains.t
  (** [propagate cs r dom] propagates the constraints associated with [r] in the
      constraint set [cs] and returns the new domain map after propagation. *)
end = struct
  module IM = Map.Make(Int)

  module CS = Set.Make(struct
      type t = Constraint.t

      let compare t1 t2 =
        Int.compare Constraint.(tag t1.repr) Constraint.(tag t2.repr)
    end)

  type t = {
    cs_set : CS.t ;
    (*** All the contraints currently active *)
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
            let cs_map = Constraint.fold_deps (cs_remove cs) cs cs_map in
            let cs' = Constraint.subst ex rr nrr cs in
            if CS.mem cs' cs_set then
              cs_map, cs_set, fresh
            else
              let cs_set = CS.add cs' cs_set in
              let cs_map = Constraint.fold_deps (cs_add cs') cs' cs_map in
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
      let cs_map =
        Constraint.fold_deps (cs_add c) c bcs.cs_map
      in
      let fresh = CS.add c bcs.fresh in
      { cs_set ; cs_map ; fresh }

  let fold_fresh f bcs acc =
    let acc = CS.fold f bcs.fresh acc in
    { bcs with fresh = CS.empty }, acc

  let propagate bcs r dom =
    match MX.find r bcs.cs_map with
    | cs -> CS.fold Constraint.propagate cs dom
    | exception Not_found -> dom
end

let extract_constraints bcs uf r t =
  match E.term_view t with
  (* BVnot is already internalized in the Shostak but we want to know about it
     without needing a round-trip through Uf *)
  | { f = Op BVnot; xs = [ x ] ; _ } ->
    let rx, exx = Uf.find uf x in
    Constraints.add bcs @@
    { repr = Constraint.hcons @@ Bnot (r, rx) ; ex = exx }
  | { f = Op BVand; xs = [ x; y ]; _ } ->
    let rx, exx = Uf.find uf x
    and ry, exy = Uf.find uf y in
    Constraints.add bcs @@
    { repr = Constraint.hcons @@ Band (r, rx, ry) ; ex = Ex.union exx exy }
  | { f = Op BVor; xs = [ x; y ]; _ } ->
    let rx, exx = Uf.find uf x
    and ry, exy = Uf.find uf y in
    Constraints.add bcs @@
    { repr = Constraint.hcons @@ Bor (r, rx, ry) ; ex = Ex.union exx exy }
  | { f = Op BVxor; xs = [ x; y ]; _ } ->
    let rx, exx = Uf.find uf x
    and ry, exy = Uf.find uf y in
    let xs = SX.singleton r in
    let xs = if SX.mem rx xs then SX.remove rx xs else SX.add rx xs in
    let xs = if SX.mem ry xs then SX.remove ry xs else SX.add ry xs in
    Constraints.add bcs @@
    { repr = Constraint.hcons @@ Bxor xs ; ex = Ex.union exx exy }
  | _ -> bcs

(** [abstract_bitlist r ex] builds a bitlist representation of the semantic
    bit-vector value [r] *)
let abstract_bitlist =
  let rec aux = function
    | [] -> Bitlist.empty
    | { Bitv.bv = Bitv.Cte n; sz } :: bs ->
      Bitlist.(exact sz n Ex.empty @ aux bs)
    | { sz; bv = (Other _ | Ext _) } :: bs ->
      Bitlist.(unknown sz Ex.empty @ aux bs)
  in fun bs -> Bitlist.add_explanation (aux bs)

let rec mk_eq ex lhs w z =
  match lhs with
  | [] -> []
  | Bitv.{ bv = Cte z'; sz } :: rest ->
    assert (Z.equal z' @@ Z.extract z (w - sz) sz);
    if sz = w then [] else
      mk_eq ex rest (w - sz) (Z.extract z 0 (w - sz))
  | Bitv.{ bv = _; sz } as lhs :: rest ->
    let lhs = Shostak.Bitv.is_mine [ lhs ] in
    let rhs = Shostak.Bitv.is_mine [
        { sz = sz ; bv = Cte (Z.extract z (w - sz) sz) }
      ] in
    if Options.get_debug_bitv () then
      Printer.print_dbg
        ~module_name:"Bitv_rel" ~function_name:"mk_eq"
        "bitlist propagated: %a = %a" X.print lhs X.print rhs;
    (Uf.LX.mkv_eq lhs rhs , ex) ::
    if sz = w then [] else
      mk_eq ex rest (w - sz) (Z.extract z 0 (w - sz))

(** [add_eqs acc r bl], where [r] is a semantic value and [bl] is a bitlist that
    applies to [r], exposes the equality [r = bl] as a list of Xliteral values
    (accumulated into [acc]) so that the union-find learns about the equality *)
let add_eqs =
  let rec aux x x_sz acc bl =
    let known = Bitlist.bits_known bl in
    let width = Bitlist.width bl in
    let nbits = Z.numbits known in
    assert (nbits <= width);
    if nbits = 0 then
      acc
    else if nbits < width then
      aux x x_sz acc (Bitlist.extract bl 0 (nbits - 1))
    else
      let nbits = Z.numbits (Z.extract (Z.lognot known) 0 width) in
      let v = Z.extract (Bitlist.value bl) nbits (width - nbits) in
      assert (nbits < width);
      let extracted = Bitv.extract x_sz nbits (width - 1) x in
      let lits = mk_eq (Bitlist.explanation bl) extracted (width - nbits) v in
      if nbits = 0 then
        lits @ acc
      else
        aux x x_sz (lits @ acc) (Bitlist.extract bl 0 (nbits - 1))
  in
  fun acc x bl ->
    aux x (Bitlist.width bl) acc bl

(* Propagate:

   - The constraints that were never propagated since they were added (this
      includes constraints that changed due to substitutions)
   - The contraints involving variables whose domain changed since the last
      propagation *)
let propagate =
  let rec propagate changed bcs dom =
    match Domains.choose_changed dom with
    | r, dom -> (
        propagate (SX.add r changed) bcs @@
        Constraints.propagate bcs r dom
      )
    | exception Not_found -> changed, dom
  in
  fun bcs dom ->
    let bcs, dom =
      Constraints.fold_fresh Constraint.propagate bcs dom
    in
    let changed, dom = propagate SX.empty bcs dom in
    SX.fold (fun r acc ->
        add_eqs acc (Shostak.Bitv.embed r) (Domains.get r dom)
      ) changed [], dom

type t =
  { delayed : Rel_utils.Delayed.t
  ; domain : Domains.t
  ; constraints : Constraints.t
  ; congruence : Congruence.t }

let empty _ =
  { delayed = Rel_utils.Delayed.create dispatch
  ; domain = Domains.empty
  ; constraints = Constraints.empty
  ; congruence = Congruence.empty }
let assume env uf la =
  let delayed, result = Rel_utils.Delayed.assume env.delayed uf la in
  let (congruence, domain, constraints, eqs) =
    try
      let (congruence, (constraints, domain)) =
        List.fold_left (fun (cgr, (bcs, dom)) (a, _root, ex, orig) ->
            match a, orig with
            | L.Eq (rr, nrr), Th_util.Subst when is_bv_r rr ->
              Congruence.subst rr nrr cgr (fun rr nrr (bcs, dom) ->
                  let bl = abstract_bitlist (Shostak.Bitv.embed nrr) Ex.empty in
                  let dom = Domains.update Ex.empty nrr dom bl in
                  (Constraints.subst ex rr nrr bcs, Domains.subst ex rr nrr dom)
                ) (bcs, dom)
            | L.Distinct (false, [rr; nrr]), NCS (Th_bitv, _) ->
              (* We don't support [distinct] in general yet, but we must
                 support it for case splits to avoid looping.

                 Note that for 1-bit vectors (i.e. booleans), we have `x <> y`
                 iff `x = not y`. *)
              assert Stdlib.(X.type_info rr = Ty.Tbitv 1);
              let drr = abstract_bitlist (Shostak.Bitv.embed rr) Ex.empty in
              let dnrr = abstract_bitlist (Shostak.Bitv.embed nrr) Ex.empty in
              let dom = Domains.update Ex.empty rr dom drr in
              let dom = Domains.update Ex.empty nrr dom dnrr in
              let bcs =
                Constraints.add bcs @@
                { repr = Constraint.hcons @@ Bnot (rr, nrr)  ; ex }
              in
              (cgr, (bcs, dom))
            | _ -> (cgr, (bcs, dom))
          ) (env.congruence, (env.constraints, env.domain)) la
      in
      let eqs, domain = propagate constraints domain in
      if Options.get_debug_bitv () && not (Lists.is_empty eqs) then (
        Printer.print_dbg
          ~module_name:"Bitv_rel" ~function_name:"assume"
          "bitlist domain: @[%a@]" Domains.pp domain;
        Printer.print_dbg
          ~module_name:"Bitv_rel" ~function_name:"assume"
          "bitlist contraints: @[%a@]" Constraints.pp constraints;
      );
      (congruence, domain, constraints, eqs)
    with Bitlist.Inconsistent ex ->
      raise @@ Ex.Inconsistent (ex, Uf.cl_extract uf)
  in
  let assume =
    List.rev_map (fun (lit, ex) -> Sig_rel.LSem lit, ex, Th_util.Other) eqs
  in
  let result =
    { result with assume = List.rev_append assume result.assume }
  in
  { delayed ; constraints ; domain ; congruence }, result
let query _ _ _ = None
let case_split env _uf ~for_model:_ =
  (* Look for representatives with minimal, non-fully known, domain size.
     [nunk] is the number of unknown bits. *)
  let _, candidates =
    match
      Domains.fold (fun r bl acc ->
          let nunk = Bitlist.num_unknown bl in
          if nunk = 0 then
            acc
          else
            match acc with
            | Some (nunk', _) when nunk > nunk' -> acc
            | Some (nunk', xs) when nunk = nunk' ->
              Some (nunk', SX.add r xs)
            | _ -> Some (nunk, SX.singleton r)
        ) env.domain None
    with
    | Some (nunk, xs) -> nunk, xs
    | None -> 0, SX.empty
  in
  (* For now, just pick a value for the most significant bit. *)
  match SX.choose candidates with
  | r ->
    let biv = Shostak.Bitv.embed r in
    let rec aux = function
      | [] -> assert false
      | { Bitv.bv = Bitv.Cte _; _ } :: biv -> aux biv
      | part :: _ ->
        Bitv.extract part.sz (part.sz - 1) (part.sz - 1) [ part ]
    in
    let lhs = Shostak.Bitv.is_mine @@ aux biv in
    (* Just always pick zero for now. *)
    let zero = Shostak.Bitv.is_mine Bitv.[ { bv = Cte Z.zero ; sz = 1 } ] in
    if Options.get_debug_bitv () then
      Printer.print_dbg
        ~module_name:"Bitv_rel" ~function_name:"case_split"
        "[BV-CS-1] Setting %a to 0" X.print lhs;
    [ Uf.LX.mkv_eq lhs zero, true, Th_util.CS (Th_util.Th_bitv, Q.of_int 2) ]
  | exception Not_found -> []
let add env uf r t =
  let delayed, eqs = Rel_utils.Delayed.add env.delayed uf r t in
  let env, eqs =
    if is_bv_r r then
      try
        let bcs = extract_constraints env.constraints uf r t in
        let dr = abstract_bitlist (Shostak.Bitv.embed r) Ex.empty in
        let dom = Domains.update Ex.empty r env.domain dr in
        let congruence = Congruence.add r env.congruence in
        let eqs', dom = propagate bcs dom in
        { env with congruence ; constraints = bcs ; domain = dom },
        List.rev_append eqs' eqs
      with Bitlist.Inconsistent ex ->
        raise @@ Ex.Inconsistent (ex, Uf.cl_extract uf)
    else
      env, eqs
  in
  { env with delayed }, eqs
let optimizing_split _env _uf _opt_split = None
let new_terms _ = Expr.Set.empty
let instantiate ~do_syntactic_matching:_ _ env _ _ = env, []

let assume_th_elt t th_elt _ =
  match th_elt.Expr.extends with
  | Util.Bitv ->
    failwith "This Theory does not support theories extension"
  | _ -> t
