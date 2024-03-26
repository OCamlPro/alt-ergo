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
module SX = Shostak.SXH
module HX = Shostak.HX
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

module Interval_domain : Rel_utils.Domain with type t = Intervals.t = struct
  type t = Intervals.t

  let equal = Intervals.equal

  let pp = Intervals.pretty_print

  exception Inconsistent = Intervals.NotConsistent

  let add_explanation ~ex i = Intervals.add_explanation i ex

  let unknown = function
    | Ty.Tbitv n ->
      let lb = Q.zero in
      let ub = Q.of_bigint Z.(~$1 lsl n) in
      let d = Intervals.undefined Tint in
      let d = Intervals.new_borne_inf Ex.empty lb ~is_le:true d in
      let d = Intervals.new_borne_sup Ex.empty ub ~is_le:false d in
      d
    | _ -> assert false

  let intersect ~ex x y =
    match Intervals.intersect x y with
    | xy -> Intervals.add_explanation xy ex
    | exception Inconsistent ex' ->
      raise @@ Inconsistent (Ex.union ex ex')

  let lognot sz int =
    Intervals.affine_scale int
      ~coef:Q.minus_one
      ~const:(Q.of_bigint @@ Z.(~$1 lsl sz - ~$1))

  let fold_signed f { Bitv.value; negated } sz int acc =
    f value (if negated then lognot sz int else int) acc

  let fold_leaves f r int acc =
    let width =
      match X.type_info r with
      | Tbitv n -> n
      | _ -> assert false
    in
    let j, acc =
      List.fold_left (fun (j, acc) { Bitv.bv; sz } ->
          (* sz = j - i + 1 => i = j - sz + 1 *)
          let int = Intervals.extract int (j - sz + 1) j in

          let acc = match bv with
            | Bitv.Cte z ->
              (* Nothing to update, but still check for consistency *)
              ignore @@
              intersect ~ex:Ex.empty int
                (Intervals.point (Q.of_bigint z) Tint Ex.empty);
              acc
            | Other s -> fold_signed f s sz int acc
            | Ext (r, r_size, i, j) ->
              (* r<i, j> = bl -> r = ?^(r_size - j - 1) @ bl @ ?^i *)
              assert (i + r_size - j - 1 + sz = r_size);
              let lo = unknown (Tbitv i) in
              let int = Intervals.scale (Q.of_bigint @@ Z.(~$1 lsl i)) int in
              let hi = unknown (Tbitv (r_size - j - 1)) in
              let hi =
                Intervals.scale (Q.of_bigint @@ Z.(~$1 lsl Stdlib.(i + sz))) hi
              in
              fold_signed f r r_size Intervals.(add hi (add int lo)) acc
          in
          (j - sz), acc
        ) (width - 1, acc) (Shostak.Bitv.embed r)
    in
    assert (j = -1);
    acc

  let map_signed f { Bitv.value; negated } sz =
    if negated then lognot sz (f value) else f value

  let map_leaves f r =
    List.fold_left (fun ival { Bitv.bv; sz } ->
        let ival = Intervals.scale (Q.of_bigint @@ Z.(~$1 lsl sz)) ival in
        Intervals.add ival @@
        match bv with
        | Bitv.Cte z -> Intervals.point (Q.of_bigint z) Tint Ex.empty
        | Other s -> map_signed f s sz
        | Ext (s, sz', i, j) ->
          Intervals.extract (map_signed f s sz') i j
      ) (Intervals.point Q.zero Tint Ex.empty) (Shostak.Bitv.embed r)
end

module Interval_domains = Rel_utils.Domains_make(Interval_domain)

module Domain : Rel_utils.Domain with type t = Bitlist.t = struct
  (* Note: these functions are not in [Bitlist] proper in order to avoid a
     (direct) dependency from [Bitlist] to the [Shostak] module. *)

  include Bitlist

  let fold_signed f { Bitv.value; negated } bl acc =
    let bl = if negated then lognot bl else bl in
    f value bl acc

  let fold_leaves f r bl acc =
    fst @@ List.fold_left (fun (acc, bl) { Bitv.bv; sz } ->
        (* Extract the bitlist associated with the current component *)
        let mid = width bl - sz in
        let bl_tail =
          if mid = 0 then empty else
            extract bl 0 (mid - 1)
        in
        let bl = extract bl mid (width bl - 1) in

        match bv with
        | Bitv.Cte z ->
          (* Nothing to update, but still check for consistency! *)
          ignore @@ intersect ~ex:Ex.empty bl (exact sz z Ex.empty);
          acc, bl_tail
        | Other r -> fold_signed f r bl acc, bl_tail
        | Ext (r, r_size, i, j) ->
          (* r<i, j> = bl -> r = ?^(r_size - j - 1) @ bl @ ?^i *)
          assert (i + r_size - j - 1 + width bl = r_size);
          let hi = Bitlist.unknown (r_size - j - 1) Ex.empty in
          let lo = Bitlist.unknown i Ex.empty in
          fold_signed f r (hi @ bl @ lo) acc, bl_tail
      ) (acc, bl) (Shostak.Bitv.embed r)

  let map_signed f { Bitv.value; negated } =
    let bl = f value in
    if negated then lognot bl else bl

  let map_leaves f r =
    List.fold_left (fun bl { Bitv.bv; sz } ->
        concat bl @@
        match bv with
        | Bitv.Cte z -> exact sz z Ex.empty
        | Other r -> map_signed f r
        | Ext (r, _r_size, i, j) -> extract (map_signed f r) i j
      ) empty (Shostak.Bitv.embed r)

  let unknown = function
    | Ty.Tbitv n -> unknown n Ex.empty
    | _ ->
      (* Only bit-vector values can have bitlist domains. *)
      invalid_arg "unknown"
end

module Domains = Rel_utils.Domains_make(Domain)

module Constraint : sig
  include Rel_utils.Constraint

  val equal : t -> t -> bool

  val hash : t -> int

  val bvand : X.r -> X.r -> X.r -> t
  (** [bvand x y z] is the constraint [x = y & z] *)

  val bvor : X.r -> X.r -> X.r -> t
  (** [bvor x y z] is the constraint [x = y | z] *)

  val bvxor : X.r -> X.r -> X.r -> t
  (** [bvxor x y z] is the constraint [x ^ y ^ z = 0] *)

  val bvule : X.r -> X.r -> t

  val bvugt : X.r -> X.r -> t

  val propagate : ex:Ex.t -> t -> Domains.Ephemeral.t -> unit
  (** [propagate ~ex t dom] propagates the constraint [t] in domain [dom].

      The explanation [ex] justifies that the constraint [t] applies, and must
      be added to any domain that gets updated during propagation. *)

  val propagate_interval : ex:Ex.t -> t -> Interval_domains.Ephemeral.t -> unit
end = struct
  type binop =
    (* Bitwise operations *)
    | Band | Bor | Bxor

  let pp_binop ppf = function
    | Band -> Fmt.pf ppf "bvand"
    | Bor -> Fmt.pf ppf "bvor"
    | Bxor -> Fmt.pf ppf "bvxor"

  let equal_binop : binop -> binop -> bool = Stdlib.(=)

  let hash_binop : binop -> int = Hashtbl.hash

  let is_commutative = function
    | Band | Bor | Bxor -> true

  let propagate_binop ~ex dx op dy dz =
    let open Domains.Ephemeral in
    match op with
    | Band ->
      update ~ex dx (Bitlist.logand !!dy !!dz);
      (* Reverse propagation for y: if [x = y & z] then:
         - Any [1] in [x] must be a [1] in [y]
         - Any [0] in [x] that is also a [1] in [z] must be a [0] in [y]
      *)
      update ~ex dy (Bitlist.ones !!dx);
      update ~ex dy Bitlist.(logor (zeroes !!dx) (lognot (ones !!dz)));
      update ~ex dz (Bitlist.ones !!dx);
      update ~ex dz Bitlist.(logor (zeroes !!dx) (lognot (ones !!dy)))
    | Bor ->
      update ~ex dx (Bitlist.logor !!dy !!dz);
      (* Reverse propagation for y: if [x = y | z] then:
         - Any [0] in [x] must be a [0] in [y]
         - Any [1] in [x] that is also a [0] in [z] must be a [1] in [y]
      *)
      update ~ex dy (Bitlist.zeroes !!dx);
      update ~ex dy Bitlist.(logand (ones !!dx) (lognot (zeroes !!dz)));
      update ~ex dz (Bitlist.zeroes !!dx);
      update ~ex dz Bitlist.(logand (ones !!dx) (lognot (zeroes !!dy)))
    | Bxor ->
      update ~ex dx (Bitlist.logxor !!dy !!dz);
      (* x = y ^ z <-> y = x ^ z *)
      update ~ex dy (Bitlist.logxor !!dx !!dz);
      update ~ex dz (Bitlist.logxor !!dx !!dy)

  let propagate_interval_binop ~ex:_ _r _op _y _z =
    (* No interval propagation for binops yet *)
    ()

  type fun_t =
    | Fbinop of binop * X.r * X.r

  let pp_fun_t ppf = function
    | Fbinop (op, x, y) ->
      Fmt.pf ppf "%a@[(%a,@ %a)@]" pp_binop op X.print x X.print y

  let equal_fun_t f1 f2 =
    match f1, f2 with
    | Fbinop (op1, x1, y1), Fbinop (op2, x2, y2) ->
      equal_binop op1 op2 && X.equal x1 x2 && X.equal y1 y2

  let hash_fun_t = function
    | Fbinop (op, x, y) -> Hashtbl.hash (hash_binop op, X.hash x, X.hash y)

  let normalize_fun_t = function
    | Fbinop (op, x, y) when is_commutative op && X.hash_cmp x y > 0 ->
      Fbinop (op, y, x)
    | Fbinop _ as e -> e

  let fold_args_fun_t f fn acc =
    match fn with
    | Fbinop (_, x, y) -> f y (f x acc)

  let subst_fun_t rr nrr = function
    | Fbinop (op, x, y) -> Fbinop (op, X.subst rr nrr x, X.subst rr nrr y)

  let propagate_fun_t ~ex dom r f =
    let open Domains.Ephemeral in
    let get r = handle dom r in
    match f with
    | Fbinop (op, x, y) ->
      propagate_binop ~ex (get r) op (get x) (get y)

  let propagate_interval_fun_t ~ex dom r f =
    let get r = Interval_domains.Ephemeral.handle dom r in
    match f with
    | Fbinop (op, x, y) ->
      propagate_interval_binop ~ex (get r) op (get x) (get y)

  type binrel = Rule | Rugt

  let pp_binrel ppf = function
    | Rule -> Fmt.pf ppf "bvule"
    | Rugt -> Fmt.pf ppf "bvugt"

  let equal_binrel : binrel -> binrel -> bool = Stdlib.(=)

  let hash_binrel : binrel -> int = Hashtbl.hash

  let propagate_binrel ~ex:_ _op _dx _dy =
    (* No bitlist propagation for relations yet *)
    ()

  let less_than_sup ~strict iv =
    let sup, ex, is_large = Intervals.borne_sup iv in
    assert is_large;
    Intervals.new_borne_sup ex sup ~is_le:(not strict) @@
    Intervals.undefined Tint

  let greater_than_inf ~strict iv =
    let inf, ex, is_large = Intervals.borne_inf iv in
    assert is_large;
    Intervals.new_borne_inf ex inf ~is_le:(not strict) @@
    Intervals.undefined Tint

  let propagate_less_than ~ex ~strict dx dy =
    let open Interval_domains.Ephemeral in
    update ~ex dx (less_than_sup ~strict !!dy);
    update ~ex dy (greater_than_inf ~strict !!dx)

  let propagate_interval_binrel ~ex op dx dy =
    match op with
    | Rule ->
      propagate_less_than ~ex ~strict:false dx dy
    | Rugt ->
      propagate_less_than ~ex ~strict:true dy dx

  type rel_t =
    | Rbinrel of binrel * X.r * X.r

  let pp_rel_t ppf = function
    | Rbinrel (op, x, y) ->
      Fmt.pf ppf "%a@[(%a,@ %a)@]" pp_binrel op X.print x X.print y

  let equal_rel_t f1 f2 =
    match f1, f2 with
    | Rbinrel (op1, x1, y1), Rbinrel (op2, x2, y2) ->
      equal_binrel op1 op2 && X.equal x1 x2 && X.equal y1 y2

  let hash_rel_t = function
    | Rbinrel (op, x, y) -> Hashtbl.hash (hash_binrel op, X.hash x, X.hash y)

  let normalize_rel_t = function
    (* No normalization for relations yet *)
    | r -> r

  let fold_args_rel_t f r acc =
    match r with
    | Rbinrel (_op, x, y) -> f y (f x acc)

  let subst_rel_t rr nrr = function
    | Rbinrel (op, x, y) -> Rbinrel (op, X.subst rr nrr x, X.subst rr nrr y)

  let propagate_rel_t ~ex dom r =
    let open Domains.Ephemeral in
    let get r = handle dom r in
    match r with
    | Rbinrel (op, x, y) ->
      propagate_binrel ~ex op (get x) (get y)

  let propagate_interval_rel_t ~ex dom r =
    let get r = Interval_domains.Ephemeral.handle dom r in
    match r with
    | Rbinrel (op, x, y) ->
      propagate_interval_binrel ~ex op (get x) (get y)

  type repr =
    | Cfun of X.r * fun_t
    | Crel of rel_t

  let pp_repr ppf = function
    | Cfun (r, fn) ->
      Fmt.(pf ppf "%a =@ %a" (box X.print) r (box pp_fun_t) fn)
    | Crel rel ->
      pp_rel_t ppf rel

  let equal_repr c1 c2 =
    match c1, c2 with
    | Cfun (r1, f1), Cfun (r2, f2) ->
      X.equal r1 r2 && equal_fun_t f1 f2
    | Cfun _, _ | _, Cfun _ -> false

    | Crel r1, Crel r2 ->
      equal_rel_t r1 r2

  let hash_repr = function
    | Cfun (r, f) -> Hashtbl.hash (0, X.hash r, hash_fun_t f)
    | Crel r -> Hashtbl.hash (1, hash_rel_t r)

  let normalize_repr = function
    | Cfun (r, f) -> Cfun (r, normalize_fun_t f)
    | Crel r -> Crel (normalize_rel_t r)

  let fold_args_repr f c acc =
    match c with
    | Cfun (r, fn) -> fold_args_fun_t f fn (f r acc)
    | Crel r -> fold_args_rel_t f r acc

  let subst_repr rr nrr = function
    | Cfun (r, f) -> Cfun (X.subst rr nrr r, subst_fun_t rr nrr f)
    | Crel r -> Crel (subst_rel_t rr nrr r)

  let propagate_repr ~ex dom = function
    | Cfun (r, f) -> propagate_fun_t ~ex dom r f
    | Crel r -> propagate_rel_t ~ex dom r

  let propagate_interval_repr ~ex dom = function
    | Cfun (r, f) -> propagate_interval_fun_t ~ex dom r f
    | Crel r -> propagate_interval_rel_t ~ex dom r

  type t = { repr : repr ; mutable tag : int }

  let pp ppf { repr; _ } = pp_repr ppf repr

  module W = Weak.Make(struct
      type nonrec t = t

      let equal c1 c2 = equal_repr c1.repr c2.repr

      let hash c = hash_repr c.repr
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

  let cfun r f = hcons @@ Cfun (r, f)

  let cbinop op r x y = cfun r (Fbinop (op, x, y))

  let bvand = cbinop Band
  let bvor = cbinop Bor
  let bvxor = cbinop Bxor

  let crel r = hcons @@ Crel r

  let cbinrel op x y = crel (Rbinrel (op, x, y))

  let bvule = cbinrel Rule
  let bvugt = cbinrel Rugt

  let equal c1 c2 = c1.tag = c2.tag

  let hash c = Hashtbl.hash c.tag

  let compare c1 c2 = Int.compare c1.tag c2.tag

  let fold_args f c acc = fold_args_repr f c.repr acc

  let subst rr nrr c =
    hcons @@ subst_repr rr nrr c.repr

  let propagate ~ex c dom =
    propagate_repr ~ex dom c.repr

  let propagate_interval ~ex c dom =
    propagate_interval_repr ~ex dom c.repr

  let simplify_binop acts op r x y =
    let acts_add_zero r =
      let sz = match X.type_info r with Tbitv n -> n | _ -> assert false in
      acts.Rel_utils.acts_add_eq r
        (Shostak.Bitv.is_mine [ { bv = Cte Z.zero ; sz }])
    in
    match op with
    | Band | Bor when X.equal x y ->
      acts.acts_add_eq r x; true

    (* r ^ x ^ x = 0 <-> r = 0 *)
    | Bxor when X.equal x y ->
      acts_add_zero r; true
    | Bxor when X.equal r x ->
      acts_add_zero y; true
    | Bxor when X.equal r y ->
      acts_add_zero x; true

    | _ -> false

  let simplify_fun_t acts r = function
    | Fbinop (op, x, y) -> simplify_binop acts op r x y

  let simplify_binrel acts op x y =
    match op with
    | Rugt when X.equal x y ->
      acts.Rel_utils.acts_add_eq X.top X.bot;
      true
    | Rule | Rugt -> false

  let simplify_rel_t acts = function
    | Rbinrel (op, x, y) -> simplify_binrel acts op x y

  let simplify_repr acts = function
    | Cfun (r, f) -> simplify_fun_t acts r f
    | Crel r -> simplify_rel_t acts r

  let simplify c acts =
    simplify_repr acts c.repr
end

module Constraints = Rel_utils.Constraints_make(Constraint)

let extract_binop =
  let open Constraint in function
    | Sy.BVand -> Some bvand
    | BVor -> Some bvor
    | BVxor -> Some bvxor
    | _ -> None

let extract_constraints bcs uf r t =
  match E.term_view t with
  | { f = Op op; xs = [ x; y ]; _ } -> (
      match extract_binop op with
      | Some mk ->
        let rx, exx = Uf.find uf x
        and ry, exy = Uf.find uf y in
        Constraints.add
          ~ex:(Ex.union exx exy) (mk r rx ry) bcs
      | _ -> bcs
    )
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

module Any_constraint = struct
  type t =
    | Constraint of Constraint.t Rel_utils.explained
    | Structural of X.r
    (** Structural constraint associated with [X.r]. See
        {!Rel_utils.Domains.structural_propagation}. *)

  let equal a b =
    match a, b with
    | Constraint ca, Constraint cb -> Constraint.equal ca.value cb.value
    | Constraint _, Structural _ | Structural _, Constraint _ -> false
    | Structural xa, Structural xb -> X.equal xa xb

  let hash = function
    | Constraint c -> 2 * Constraint.hash c.value
    | Structural r -> 2 * X.hash r + 1

  let propagate constraint_propagate structural_propagation c d =
    match c with
    | Constraint { value; explanation = ex } ->
      constraint_propagate ~ex value d
    | Structural r ->
      structural_propagation d r
end

module QC = Uqueue.Make(Any_constraint)

(* Compute the number of most significant bits shared by [inf] and [sup].

   Requires: [inf <= sup]
   Ensures:
    result is the greatest integer <= sz such that
    inf<sz - result .. sz> = sup<sz - result .. sz>

    In particular, [result = sz] iff [inf = sup] and [result = 0] iff the most
    significant bits of [inf] and [sup] differ. *)
let rec shared_msb sz inf sup =
  let numbits_inf = Z.numbits inf in
  let numbits_sup = Z.numbits sup in
  assert (numbits_inf <= numbits_sup);
  if numbits_inf = numbits_sup then
    (* Top [sz - numbits_inf] bits are 0 in both; look at 1s *)
    if numbits_inf = 0 then
      sz
    else
      sz - numbits_inf +
      shared_msb numbits_inf
        (Z.extract (Z.lognot sup) 0 numbits_inf)
        (Z.extract (Z.lognot inf) 0 numbits_inf)
  else
    (* Top [sz - numbits_sup] are 0 in both, the next significant bit differs *)
    sz - numbits_sup

(* If m and M are the minimal and maximal values of an union of intervals, the
   longest sequence of most significant bits shared between m and M can be fixed
   in the bit-vector domain; see "Is to BVs" in section 4.1 of

   Sharpening Constraint Programming approaches for Bit-Vector Theory.
   Zakaria Chihani, Bruno Marre, François Bobot, Sébastien Bardin.
   CPAIOR 2017. International Conference on AI and OR Techniques in
   Constraint Programming for Combinatorial Optimization Problems, Jun
   2017, Padova, Italy.
   https://cea.hal.science/cea-01795779/document *)
let constrain_bitlist_from_interval bv int =
  let open Domains.Ephemeral in
  let inf, inf_ex, inf_large = Intervals.borne_inf int in
  assert inf_large;
  let inf = Q.to_bigint inf in
  let sup, sup_ex, sup_large = Intervals.borne_sup int in
  assert sup_large;
  let sup = Q.to_bigint sup in

  let sz = Bitlist.width !!bv in
  let nshared = shared_msb sz inf sup in
  if nshared > 0 then
    let ex = Ex.union inf_ex sup_ex in
    let shared_bl =
      Bitlist.exact nshared (Z.extract inf (sz - nshared) nshared) ex
    in
    update ~ex bv @@
    Bitlist.concat shared_bl (Bitlist.unknown (sz - nshared) Ex.empty)

(* These are helpers for readability because [Intervals.mk_closed] makes my
   brain melt *)

type inequality = Large | Strict

let is_large = function Large -> true | Strict -> false

type bound = Infinite | Bounded of Q.t * inequality

let large n = Bounded (n, Large)

let strict n = Bounded (n, Strict)

let strict_z n = strict (Q.of_bigint n)

let infinite = Infinite

let interval ~ex lb ub =
  match lb, ub with
  | Infinite, Infinite -> Intervals.undefined Tint
  | Infinite, Bounded (ub, ineq) ->
    Intervals.new_borne_sup ex ub ~is_le:(is_large ineq)
      (Intervals.undefined Tint)
  | Bounded (lb, ineq), Infinite ->
    Intervals.new_borne_inf ex lb ~is_le:(is_large ineq)
      (Intervals.undefined Tint)
  | Bounded (lb, lineq), Bounded (ub, uineq) ->
    Intervals.mk_closed
      lb ub
      (is_large lineq) (is_large uineq)
      ex ex Tint

(* Algorithm 1 from "Sharpening Constraint Programming approaches for
   Bit-Vector Theory". *)
let constrain_interval_from_bitlist int bv =
  let open Interval_domains.Ephemeral in
  let ex = Bitlist.explanation bv in
  (* [exclude i1 i2] being [i2 \ i1] also makes my brain hurt *)
  let remove i2 i1 = Intervals.exclude i1 i2 in
  update ~ex int @@
  List.fold_left (fun acc ((lb, _ex_lb), (ub, _ex_ub)) ->
      (* Note: the bounds adjustment is expressed by removing specific
         intervals that are forbidden by the bitlist domain. This is always
         correct independently of the bounds' explanations: we only use the
         bounds to guide us on *which* intervals to remove. Hence, we just
         ignore the bounds' explanations. *)
      let acc =
        match lb with
        | None -> assert false
        | Some (lb, eps) ->
          assert (Q.equal eps Q.zero);
          let lb_z = Q.to_bigint lb in
          match Bitlist.increase_lower_bound bv (Q.to_bigint lb) with
          | new_lb_z when Z.compare new_lb_z lb_z > 0 ->
            (* lower bound increased; remove [lb, new_lb[ *)
            remove acc @@ interval ~ex (large lb) (strict_z new_lb_z)
          | new_lb_z ->
            (* no change *)
            assert (Z.equal new_lb_z lb_z);
            acc
          | exception Not_found ->
            (* No value larger than lb matches the bit-pattern *)
            remove acc @@ interval ~ex (large lb) infinite
      in
      let acc =
        match ub with
        | None -> assert false
        | Some (ub, eps) ->
          assert (Q.equal eps Q.zero);
          let ub_z = Q.to_bigint ub in
          match Bitlist.decrease_upper_bound bv ub_z with
          | new_ub_z when Z.compare new_ub_z ub_z < 0 ->
            (* upper bound decreased; remove ]new_ub, ub] *)
            remove acc @@ interval ~ex (strict_z new_ub_z) (large ub)
          | new_ub_z ->
            (* no change *)
            assert (Z.equal new_ub_z ub_z);
            acc
          | exception Not_found ->
            (* No value smaller than ub matches the bit-pattern *)
            remove acc @@ interval ~ex infinite (large ub)
      in
      acc
    ) !!int (Intervals.bounds_of !!int)

let propagate_bitlist queue touched bcs dom =
  let touch_c c = QC.push queue (Constraint c) in
  let touch r =
    HX.replace touched r ();
    QC.push queue (Structural r);
    Constraints.iter_parents touch_c r bcs
  in
  try
    while true do
      Domains.Ephemeral.iter_changed touch dom;
      Domains.Ephemeral.clear_changed dom;
      Any_constraint.propagate
        Constraint.propagate
        Domains.Ephemeral.structural_propagation
        (QC.pop queue) dom
    done
  with QC.Empty -> ()

let propagate_intervals queue touched bcs dom =
  let touch_c c = QC.push queue (Constraint c) in
  let touch r =
    HX.replace touched r ();
    QC.push queue (Structural r);
    Constraints.iter_parents touch_c r bcs
  in
  try
    while true do
      Interval_domains.Ephemeral.iter_changed touch dom;
      Interval_domains.Ephemeral.clear_changed dom;
      Any_constraint.propagate
        Constraint.propagate_interval
        Interval_domains.Ephemeral.structural_propagation
        (QC.pop queue) dom
    done
  with QC.Empty -> ()

let propagate_all eqs bcs bdom idom =
  (* Call [simplify_pending] first because it can remove constraints from the
     pending set. *)
  let eqs, bcs = Constraints.simplify_pending eqs bcs in
  (* Optimization to avoid unnecessary allocations *)
  let do_all = Constraints.has_pending bcs in
  let do_bitlist = do_all || Domains.has_changed bdom in
  let do_intervals = do_all || Interval_domains.has_changed idom in
  let do_any = do_bitlist || do_intervals in
  if do_any then
    let queue = QC.create 17 in
    let touch_pending queue =
      Constraints.iter_pending (fun c -> QC.push queue (Constraint c)) bcs
    in
    let bitlist_changed = HX.create 17 in
    let touched = HX.create 17 in
    let bdom = Domains.edit bdom in
    let idom = Interval_domains.edit idom in

    (* First, we propagate the pending constraints to both domains. Changes in
       the bitlist domain are used to shrink the interval domains. *)
    touch_pending queue;
    propagate_bitlist queue touched bcs bdom;
    assert (QC.is_empty queue);

    touch_pending queue;
    HX.iter (fun r () ->
        HX.replace bitlist_changed r ();
        constrain_interval_from_bitlist
          Interval_domains.Ephemeral.(handle idom r)
          Domains.Ephemeral.(!!(handle bdom r))
      ) touched;
    HX.clear touched;
    propagate_intervals queue touched bcs idom;
    assert (QC.is_empty queue);

    (* Now the interval domain is stable, but the new intervals may have an
       impact on the bitlist domains, so we must shrink them again when
       applicable. We repeat until a fixpoint is reached. *)
    let bcs = Constraints.clear_pending bcs in
    while HX.length touched > 0 do
      HX.iter (fun r () ->
          constrain_bitlist_from_interval
            Domains.Ephemeral.(handle bdom r)
            Interval_domains.Ephemeral.(!!(handle idom r))
        ) touched;
      HX.clear touched;
      propagate_bitlist queue touched bcs bdom;
      assert (QC.is_empty queue);

      HX.iter (fun r () ->
          HX.replace bitlist_changed r ();
          constrain_interval_from_bitlist
            Interval_domains.Ephemeral.(handle idom r)
            Domains.Ephemeral.(!!(handle bdom r))
        ) touched;
      HX.clear touched;
      propagate_intervals queue touched bcs idom;
      assert (QC.is_empty queue);
    done;

    let eqs =
      HX.fold (fun r () acc ->
          let d = Domains.Ephemeral.(!!(handle bdom r)) in
          add_eqs acc (Shostak.Bitv.embed r) d
        ) bitlist_changed eqs
    in

    eqs, bcs, Domains.snapshot bdom, Interval_domains.snapshot idom
  else
    eqs, bcs, bdom, idom

type t =
  { delayed : Rel_utils.Delayed.t
  ; domain : Domains.t
  ; interval_domain : Interval_domains.t
  ; constraints : Constraints.t
  ; size_splits : Q.t }

let empty _ =
  { delayed = Rel_utils.Delayed.create dispatch
  ; domain = Domains.empty
  ; interval_domain = Interval_domains.empty
  ; constraints = Constraints.empty
  ; size_splits = Q.one }

let assume env uf la =
  let delayed, result = Rel_utils.Delayed.assume env.delayed uf la in
  let (domain, interval_domain, constraints, eqs, size_splits) =
    try
      let ((constraints, domain, int_domain), eqs, size_splits) =
        List.fold_left (fun ((bcs, dom, idom), eqs, ss) (a, _root, ex, orig) ->
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
              let dom = Domains.subst ~ex rr nrr dom in
              let idom = Interval_domains.subst ~ex rr nrr idom in
              let bcs = Constraints.subst ~ex rr nrr bcs in
              ((bcs, dom, idom), eqs, ss)
            | Builtin (is_true, BVULE, [x; y]), _ ->
              let x, exx = Uf.find_r uf x in
              let y, exy = Uf.find_r uf y in
              let ex = Ex.union ex @@ Ex.union exx exy in
              let c =
                if is_true then
                  Constraint.bvule x y
                else
                  Constraint.bvugt x y
              in
              let bcs = Constraints.add ~ex c bcs in
              ((bcs, dom, idom), eqs, ss)
            | L.Distinct (false, [rr; nrr]), _ when is_1bit rr ->
              (* We don't (yet) support [distinct] in general, but we must
                 support it for case splits to avoid looping.

                 We are a bit more general and support it for 1-bit vectors, for
                 which `distinct` can be expressed using `bvnot`. *)
              let not_nrr =
                Shostak.Bitv.is_mine (Bitv.lognot (Shostak.Bitv.embed nrr))
              in
              ((bcs, dom, idom), (Uf.LX.mkv_eq rr not_nrr, ex) :: eqs, ss)
            | _ -> ((bcs, dom, idom), eqs, ss)
          )
          ((env.constraints, env.domain, env.interval_domain)
          , []
          , env.size_splits)
          la
      in
      let eqs, constraints, domain, int_domain =
        propagate_all eqs constraints domain int_domain
      in
      if Options.get_debug_bitv () && not (Lists.is_empty eqs) then (
        Printer.print_dbg
          ~module_name:"Bitv_rel" ~function_name:"assume"
          "bitlist domain: @[%a@]" Domains.pp domain;
        Printer.print_dbg
          ~module_name:"Bitv_rel" ~function_name:"assume"
          "interval domain: @[%a@]" Interval_domains.pp int_domain;
        Printer.print_dbg
          ~module_name:"Bitv_rel" ~function_name:"assume"
          "bitlist constraints: @[%a@]" Constraints.pp constraints;
      );
      (domain, int_domain, constraints, eqs, size_splits)
    with Bitlist.Inconsistent ex | Intervals.NotConsistent ex ->
      raise @@ Ex.Inconsistent (ex, Uf.cl_extract uf)
  in
  let assume =
    List.rev_map (fun (lit, ex) -> Literal.LSem lit, ex, Th_util.Other) eqs
  in
  let result =
    { result with assume = List.rev_append assume result.assume }
  in
  { delayed ; constraints ; domain ; interval_domain ; size_splits }, result

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
        match Domains.fold_leaves f_acc env.domain None with
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
    | Tbitv _ -> (
        try
          let dom = Domains.add r env.domain in
          let idom = Interval_domains.add r env.interval_domain in
          let bcs = extract_constraints env.constraints uf r t in
          let eqs, bcs, dom, idom = propagate_all eqs bcs dom idom in
          { env with
            constraints = bcs ;
            domain = dom ;
            interval_domain = idom ;
          }, eqs
        with Bitlist.Inconsistent ex | Intervals.NotConsistent ex ->
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

module Test = struct
  let shared_msb = shared_msb
end
