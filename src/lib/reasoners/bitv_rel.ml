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

let timer = Timers.M_Bitv

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
  (** The type of domain maps. A domain map maps each representative (semantic
      value, of type [X.r]) to its associated domain.

      The keys of the domain maps are expected to be current *class
      representatives*, i.e.  normal forms wrt to the `Uf` module, in which
      case we say the domain map is *normalized*. Use `subst` to ensure that
      domain maps stay normalized. *)

  val pp : t Fmt.t
  (** Pretty-printer for domain maps. *)

  val empty : t
  (** Returns an empty domain map. *)

  val update : Ex.t -> X.r -> t -> Bitlist.t -> t
  (** [update ex r d bl] intersects the domain of [r] with bitlist [bl].

      The explanation [ex] justifies that [bl] applies to [r].

      @raise Bitlist.Inconsistent if the new domain is empty. *)

  val get : X.r -> t -> Bitlist.t
  (** [get r d] returns the bitlist currently associated with [r] in [d].

      @raise Not_found if there is no bitlist associated with [r] in [d]. *)

  val subst : Ex.t -> X.r -> X.r -> t -> t
  (** [subst ex p v d] replaces all the instances of [p] with [v] in any domain,
      and merges the corresponding bitlists.

      Use this to ensure that the representation is always normalized.

      The explanation [ex] justifies the equality [p = v].

      @raise Bitlist.Inconsistent if this causes any domain in [d] to become
        empty. *)

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
    (** Mapping from semantic values to their bitlist domain.

        Note: this mapping only contains domain for leaves (i.e. uninterpreted
        terms or AC symbols); domains associated with more complex semantic
        values are rebuilt on-the-fly using the structure of said semantic
        values. *)
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

  let update_leaf ex r t bl =
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

  let update_signed ex { Bitv.value; negated } t bl =
    let bl = if negated then Bitlist.lognot bl else bl in
    update_leaf ex value t bl

  let update ex r t bl =
    fst @@ List.fold_left (fun (t, bl) { Bitv.bv; sz } ->
        (* Extract the bitlist associated with the current component *)
        let mid = Bitlist.width bl - sz in
        let bl_tail =
          if mid = 0 then Bitlist.empty else
            Bitlist.extract bl 0 (mid - 1)
        in
        let bl = Bitlist.extract bl mid (Bitlist.width bl - 1) in

        match bv with
        | Bitv.Cte z ->
          (* Nothing to update, but still check for consistency! *)
          ignore @@ Bitlist.intersect bl (Bitlist.exact sz z Ex.empty) ex;
          t, bl_tail
        | Other r -> update_signed ex r t bl, bl_tail
        | Ext (r, r_size, i, j) ->
          (* r<i, j> = bl -> r = ?^(r_size - j - 1) @ bl @ ?^i *)
          assert (i + r_size - j - 1 + Bitlist.width bl = r_size);
          let hi = Bitlist.unknown (r_size - j - 1) Ex.empty in
          let lo = Bitlist.unknown i Ex.empty in
          update_signed ex r t Bitlist.(hi @ bl @ lo), bl_tail
      ) (t, bl) (Shostak.Bitv.embed r)

  let get_leaf r t =
    try MX.find r t.bitlists with
    | Not_found ->
      match X.type_info r with
      | Tbitv n -> Bitlist.unknown n Explanation.empty
      | _ -> assert false

  let get_signed { Bitv.value; negated } t =
    let bl = get_leaf value t in
    if negated then Bitlist.lognot bl else bl

  let get r t =
    List.fold_left (fun bl { Bitv.bv; sz } ->
        Bitlist.concat bl @@
        match bv with
        | Bitv.Cte z -> Bitlist.exact sz z Ex.empty
        | Other r -> get_signed r t
        | Ext (r, _r_size, i, j) -> Bitlist.extract (get_signed r t) i j
      ) Bitlist.empty (Shostak.Bitv.embed r)

  let subst ex rr nrr t =
    match MX.find rr t.bitlists with
    | bl ->
      (* The substitution code for constraints requires that we properly update
         the [changed] field here: if the domain of [rr] has changed,
         constraints that applied to [rr] will apply to [nrr] after
         substitution and must be propagated again. *)
      let changed =
        if SX.mem rr t.changed then
          SX.add nrr t.changed
        else
          t.changed
      in
      let t =
        { changed = SX.remove rr changed
        ; bitlists = MX.remove rr t.bitlists
        }
      in
      update ex nrr t bl
    | exception Not_found -> t

  let choose_changed t =
    let r = SX.choose t.changed in
    r, { t with changed = SX.remove r t.changed }

  let fold f t = MX.fold f t.bitlists
end

module Constraint : sig
  include Rel_utils.Constraint

  val bvand : X.r -> X.r -> X.r -> t
  (** [bvand x y z] is the constraint [x = y & z] *)

  val bvor : X.r -> X.r -> X.r -> t
  (** [bvor x y z] is the constraint [x = y | z] *)

  val bvxor : X.r -> X.r -> X.r -> t
  (** [bvxor x y z] is the constraint [x ^ y ^ z = 0] *)

  val bvnot : X.r -> X.r -> t
  (** [bvnot x y] is the constraint [x = not y] *)

  val propagate : ex:Ex.t -> t -> Domains.t -> Domains.t
  (** [propagate ~ex t dom] propagates the constraint [t] in domain [dom].

      The explanation [ex] justifies that the constraint [t] applies, and must
      be added to any domain that gets updated during propagation. *)
end = struct
  type repr =
    | Band of X.r * X.r * X.r
    (** [Band (x, y, z)] represents [x = y & z] *)
    | Bor of X.r * X.r * X.r
    (** [Bor (x, y, z)] represents [x = y | z] *)
    | Bxor of SX.t
    (** [Bxor {x1, ..., xn}] represents [x1 ^ ... ^ xn = 0] *)
    | Bnot of X.r * X.r
    (** [Bnot (x, y)] represents [x = not y] *)

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

  type t = { repr : repr ; mutable tag : int }

  module W = Weak.Make(struct
      type nonrec t = t

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

  let pp_repr ppf = function
    | Band (x, y, z) ->
      Fmt.pf ppf "%a & %a = %a" X.print y X.print z X.print x
    | Bor (x, y, z) ->
      Fmt.pf ppf "%a | %a = %a" X.print y X.print z X.print x
    | Bxor xs ->
      Fmt.(iter ~sep:(any " ^@ ") SX.iter X.print |> box) ppf xs;
      Fmt.pf ppf " = 0"
    | Bnot (x, y) ->
      Fmt.pf ppf "%a = ~%a" X.print x X.print y

  (* TODO: for bitwise constraints (eg Band, Bor, Bxor)
      on initialisation and also after substitution
      we should split the domain
  *)

  let subst_repr rr nrr = function
    | Band (x, y, z) ->
      let x = X.subst rr nrr x
      and y = X.subst rr nrr y
      and z = X.subst rr nrr z in
      Band (x, y, z)
    | Bor (x, y, z) ->
      let x = X.subst rr nrr x
      and y = X.subst rr nrr y
      and z = X.subst rr nrr z in
      Bor (x, y, z)
    | Bxor xs ->
      Bxor (
        SX.fold (fun r xs ->
            let r = X.subst rr nrr r in
            if SX.mem r xs then SX.remove r xs else SX.add r xs
          ) xs SX.empty
      )
    | Bnot (x, y) ->
      let x = X.subst rr nrr x
      and y = X.subst rr nrr y in
      Bnot (x, y)

  let pp ppf { repr; _ } = pp_repr ppf repr

  let compare { tag = t1; _ } { tag = t2; _ } = Stdlib.compare t1 t2

  let subst rr nrr c =
    hcons @@ subst_repr rr nrr c.repr

  let fold_args f { repr; _ } acc =
    match repr with
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

  let propagate ~ex { repr; _ } dom =
    Steps.incr CP;
    match repr with
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

  let bvand x y z = hcons @@ Band (x, y, z)
  let bvor x y z = hcons @@ Bor (x, y, z)
  let bvxor x y z =
    let xs = SX.singleton x in
    let xs = if SX.mem y xs then SX.remove y xs else SX.add y xs in
    let xs = if SX.mem z xs then SX.remove z xs else SX.add z xs in
    hcons @@ Bxor xs
  let bvnot x y = hcons @@ Bnot (x, y)
end

module Constraints = Rel_utils.Constraints_make(Constraint)

let extract_constraints bcs uf r t =
  match E.term_view t with
  (* BVnot is already internalized in the Shostak but we want to know about it
     without needing a round-trip through Uf *)
  | { f = Op BVnot; xs = [ x ] ; _ } ->
    let rx, exx = Uf.find uf x in
    Constraints.add ~ex:exx (Constraint.bvnot r rx) bcs
  | { f = Op BVand; xs = [ x; y ]; _ } ->
    let rx, exx = Uf.find uf x
    and ry, exy = Uf.find uf y in
    Constraints.add ~ex:(Ex.union exx exy) (Constraint.bvand r rx ry) bcs
  | { f = Op BVor; xs = [ x; y ]; _ } ->
    let rx, exx = Uf.find uf x
    and ry, exy = Uf.find uf y in
    Constraints.add ~ex:(Ex.union exx exy) (Constraint.bvor r rx ry) bcs
  | { f = Op BVxor; xs = [ x; y ]; _ } ->
    let rx, exx = Uf.find uf x
    and ry, exy = Uf.find uf y in
    Constraints.add ~ex:(Ex.union exx exy) (Constraint.bvxor r rx ry) bcs
  | _ -> bcs

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

   - The constraints that were never propagated since they were added
   - The constraints involving variables whose domain changed since the last
      propagation

   Iterate until fixpoint is reached. *)
let propagate =
  let rec propagate changed bcs dom =
    match Constraints.next_pending bcs with
    | { value; explanation = ex }, bcs ->
      let dom = Constraint.propagate ~ex value dom in
      propagate changed bcs dom
    | exception Not_found ->
      match Domains.choose_changed dom with
      | r, dom ->
        propagate (SX.add r changed) (Constraints.notify_leaf r bcs) dom
      | exception Not_found ->
        changed, bcs, dom
  in
  fun bcs dom ->
    let changed, bcs, dom = propagate SX.empty bcs dom in
    SX.fold (fun r acc ->
        add_eqs acc (Shostak.Bitv.embed r) (Domains.get r dom)
      ) changed [], bcs, dom

type t =
  { delayed : Rel_utils.Delayed.t
  ; domain : Domains.t
  ; constraints : Constraints.t
  ; size_splits : Q.t }

let empty _ =
  { delayed = Rel_utils.Delayed.create dispatch
  ; domain = Domains.empty
  ; constraints = Constraints.empty
  ; size_splits = Q.one }

let assume env uf la =
  let delayed, result = Rel_utils.Delayed.assume env.delayed uf la in
  let (domain, constraints, eqs, size_splits) =
    try
      let ((constraints, domain), size_splits) =
        List.fold_left (fun ((bcs, dom), ss) (a, _root, ex, orig) ->
            let ss =
              match orig with
              | Th_util.CS (Th_bitv, n) -> Q.(ss * n)
              | _ -> ss
            in
            let is_1bit r =
              match X.type_info r with
              | Tbitv 1 -> true
              | _ -> false
            in
            match a, orig with
            | L.Eq (rr, nrr), Subst when is_bv_r rr ->
              let dom = Domains.subst ex rr nrr dom in
              let bcs = Constraints.subst ~ex rr nrr bcs in
              ((bcs, dom), ss)
            | L.Distinct (false, [rr; nrr]), _ when is_1bit rr ->
              (* We don't (yet) support [distinct] in general, but we must
                 support it for case splits to avoid looping.

                 We are a bit more general and support it for 1-bit vectors, for
                 which `distinct` can be expressed using `bvnot`.

                 Note that we are not guaranteed that the arguments are already
                 in normal form! *)
              let rr, exrr = Uf.find_r uf rr in
              let nrr, exnrr = Uf.find_r uf nrr in
              let ex = Ex.union ex (Ex.union exrr exnrr) in
              let bcs =
                Constraints.add ~ex (Constraint.bvnot rr nrr) bcs
              in
              ((bcs, dom), ss)
            | _ -> ((bcs, dom), ss)
          )
          ((env.constraints, env.domain), env.size_splits)
          la
      in
      let eqs, constraints, domain = propagate constraints domain in
      if Options.get_debug_bitv () && not (Lists.is_empty eqs) then (
        Printer.print_dbg
          ~module_name:"Bitv_rel" ~function_name:"assume"
          "bitlist domain: @[%a@]" Domains.pp domain;
        Printer.print_dbg
          ~module_name:"Bitv_rel" ~function_name:"assume"
          "bitlist constraints: @[%a@]" Constraints.pp constraints;
      );
      (domain, constraints, eqs, size_splits)
    with Bitlist.Inconsistent ex ->
      raise @@ Ex.Inconsistent (ex, Uf.cl_extract uf)
  in
  let assume =
    List.rev_map (fun (lit, ex) -> Literal.LSem lit, ex, Th_util.Other) eqs
  in
  let result =
    { result with assume = List.rev_append assume result.assume }
  in
  { delayed ; constraints ; domain ; size_splits }, result

let query _ _ _ = None

let case_split env _uf ~for_model =
  if not for_model && Stdlib.(env.size_splits >= Options.get_max_split ()) then
    []
  else
    (* Look for representatives with minimal, non-fully known, domain size.

       We first look among the constrained variables, then if there are no
       constrained variables, all the remaining variables.

       [nunk] is the number of unknown bits. *)
    let f_acc r bl acc =
      let nunk = Bitlist.num_unknown bl in
      if nunk = 0 then
        acc
      else
        match acc with
        | Some (nunk', _) when nunk > nunk' -> acc
        | Some (nunk', xs) when nunk = nunk' ->
          Some (nunk', SX.add r xs)
        | _ -> Some (nunk, SX.singleton r)
    in
    let _, candidates =
      match
        Constraints.fold_args (fun r acc ->
            List.fold_left (fun acc { Bitv.bv; _ } ->
                match bv with
                | Bitv.Cte _ -> acc
                | Other r | Ext (r, _, _, _) ->
                  let bl = Domains.get r.value env.domain in
                  f_acc r.value bl acc
              ) acc (Shostak.Bitv.embed r)
          ) env.constraints None
      with
      | Some (nunk, xs) -> nunk, xs
      | None ->
        match Domains.fold f_acc env.domain None with
        | Some (nunk, xs) -> nunk, xs
        | None -> 0, SX.empty
    in
    (* For now, just pick a value for the most significant bit. *)
    match SX.choose candidates with
    | r ->
      let bl = Domains.get r env.domain in
      let w = Bitlist.width bl in
      let unknown = Z.extract (Z.lognot @@ Bitlist.bits_known bl) 0 w in
      let bitidx = Z.numbits unknown  - 1 in
      let lhs =
        Shostak.Bitv.is_mine @@
        Bitv.extract w bitidx bitidx (Shostak.Bitv.embed r)
      in
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
    match X.type_info r with
    | Tbitv n -> (
        try
          let dr = Bitlist.unknown n Ex.empty in
          let dom = Domains.update Ex.empty r env.domain dr in
          let bcs = extract_constraints env.constraints uf r t in
          let eqs', bcs, dom = propagate bcs dom in
          { env with constraints = bcs ; domain = dom },
          List.rev_append eqs' eqs
        with Bitlist.Inconsistent ex ->
          raise @@ Ex.Inconsistent (ex, Uf.cl_extract uf)
      )
    | _ -> env, eqs
  in
  { env with delayed }, eqs

let optimizing_objective _env _uf _o = None

let new_terms _ = Expr.Set.empty

let instantiate ~do_syntactic_matching:_ _ env _ _ = env, []

let assume_th_elt t th_elt _ =
  match th_elt.Expr.extends with
  | Util.Bitv ->
    failwith "This Theory does not support theories extension"
  | _ -> t
