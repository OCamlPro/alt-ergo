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

module E = Expr
module Ex = Explanation
module Sy = Symbols
module X = Shostak.Combine
module SX = Shostak.SXH
module MX = Shostak.MXH
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

let bitwidth r =
  match X.type_info r with Tbitv n -> n | _ -> assert false

let const sz n =
  Shostak.Bitv.is_mine [ { bv = Cte (Z.extract n 0 sz); sz } ]

module Interval_domain = struct
  type t = Intervals.Int.t

  let equal = Intervals.Int.equal

  let pp = Intervals.Int.pp

  exception Inconsistent of Explanation.t

  let add_explanation = Intervals.Int.add_explanation

  type constant = Z.t

  let constant n = Intervals.Int.of_bounds (Closed n) (Closed n)

  let filter_ty = is_bv_ty

  let unknown = function
    | Ty.Tbitv n ->
      Intervals.Int.of_bounds
        (Closed Z.zero) (Open Z.(~$1 lsl n))
    | ty ->
      Fmt.invalid_arg "unknown: only bit-vector types are supported; got %a"
        Ty.print ty

  let intersect x y =
    match Intervals.Int.intersect x y with
    | Empty ex ->
      raise @@ Inconsistent ex
    | NonEmpty u -> u

  let lognot sz int =
    Intervals.Int.extract ~ofs:0 ~len:sz @@ Intervals.Int.lognot int

  let add_offset d cte =
    Intervals.Int.add d (Intervals.Int.of_bounds (Closed cte) (Closed cte))

  let sub_offset d cte =
    Intervals.Int.sub d (Intervals.Int.of_bounds (Closed cte) (Closed cte))
end

type 'a explained = { value : 'a ; explanation : Explanation.t }

let explained ~ex value = { value ; explanation = ex }

module ExplainedOrdered(V : Rel_utils.OrderedType) :
  Rel_utils.OrderedType with type t = V.t explained =
struct
  type t = V.t explained

  let pp ppf { value; _ } = V.pp ppf value

  let compare { value = v1; _ } { value = v2; _ } = V.compare v1 v2

  module Set = Set.Make(struct
      type nonrec t = t

      let compare = compare
    end)

  module Map = Map.Make(struct
      type nonrec t = t

      let compare = compare
    end)
end

module BitvNormalForm = struct
  (** Normal form for bit-vector values.

      We decompose non-constant bit-vector compositions as a variable part,
      where all constant bits are set to [0] and all high constant bits are
      chopped off, and an offset with all the constant bits. We consider the
      variable part atomic if it is a single non-negated variable.

      Assuming [x] and [y] are bit-vectors of width 2:
      - [101 @ x] is [x + 10100] ;
      - [10 @ x @ 01] is [(x @ 00) + 100001] ;
      - [10 @ y<0, 0> @ y<1, 1>] is [(y<0, 0> @ y<1>1) + 1000] ;
      - [10 @ x @ 11 @ y] is [(x @ 00 @ y) + 10001100] *)

  type constant = Z.t

  type atom = X.r

  type composite = X.r

  type t =
    | Constant of constant
    | Atom of atom * constant
    | Composite of composite * constant

  type expr = X.r

  let normal_form r =
    let rec loop cte rev_acc = function
      | [] -> (
          match rev_acc with
          | [] ->
            Constant cte
          | [ { Bitv.bv = Bitv.Other { value ; negated = false }; _ } ] ->
            Atom (value, cte)
          | _ ->
            Composite (Shostak.Bitv.is_mine (List.rev rev_acc), cte)
        )
      | { Bitv.bv = Bitv.Cte n ; sz } :: bv' ->
        let cte = Z.(cte lsl sz lor n) in
        let acc =
          match rev_acc with
          | [] -> []
          | _ -> { Bitv.bv = Bitv.Cte Z.zero ; sz } :: rev_acc
        in
        loop cte acc bv'
      | x :: bv' ->
        let cte = Z.(cte lsl x.sz) in
        loop cte (x :: rev_acc) bv'
    in loop Z.zero [] (Shostak.Bitv.embed r)
end

module Constraint : sig
  type binop =
    (* Bitwise operations *)
    | Band | Bor | Bxor
    (* Arithmetic operations *)
    | Badd | Bmul | Budiv | Burem
    (* Shift operations *)
    | Bshl | Blshr

  type fun_t =
    | Fbinop of binop * X.r * X.r

  type binrel = Rule | Rugt

  type rel_t =
    | Rbinrel of binrel * X.r * X.r

  type view =
    | Cfun of X.r * fun_t
    | Crel of rel_t

  type t

  val view : t -> view

  val pp : t Fmt.t
  (** Pretty-printer for constraints. *)

  val equal : t -> t -> bool

  val hash : t -> int

  val compare : t -> t -> int
  (** Comparison function for constraints. The comparison function is
      arbitrary and has no semantic meaning. You should not depend on any of
      its properties, other than it defines an (arbitrary) total order on
      constraint representations. *)

  val fold_args : (X.r -> 'a -> 'a) -> t -> 'a -> 'a

  val bvand : X.r -> X.r -> X.r -> t
  (** [bvand x y z] is the constraint [x = y & z] *)

  val bvor : X.r -> X.r -> X.r -> t
  (** [bvor x y z] is the constraint [x = y | z] *)

  val bvxor : X.r -> X.r -> X.r -> t
  (** [bvxor x y z] is the constraint [x ^ y ^ z = 0] *)

  val bvadd : X.r -> X.r -> X.r -> t
  (** [bvadd r x y] is the constraint [r = x + y] *)

  val bvsub : X.r -> X.r -> X.r -> t
  (** [bvsub r x y] is the constraint [r = x - y] *)

  val bvmul : X.r -> X.r -> X.r -> t
  (** [bvmul r x y] is the constraint [r = x * y] *)

  val bvudiv : X.r -> X.r -> X.r -> t
  (** [bvudir r x y] is the constraint [r = x / y]

      This uses the convention that [x / 0] is [-1]. *)

  val bvurem : X.r -> X.r -> X.r -> t
  (** [bvurem r x y] is the constraint [r = x % y], where [x % y] is the
      remainder of euclidean division.

      This uses the convention that [x % 0] is [x]. *)

  val bvshl : X.r -> X.r -> X.r -> t
  (** [bvshl r x y] is the constraint [r = x << y] *)

  val bvlshr : X.r -> X.r -> X.r -> t
  (** [bvshl r x y] is the constraint [r = x >> y] *)

  val bvule : X.r -> X.r -> t

  val bvugt : X.r -> X.r -> t
end = struct
  type binop =
    (* Bitwise operations *)
    | Band | Bor | Bxor
    (* Arithmetic operations *)
    | Badd | Bmul | Budiv | Burem
    (* Shift operations *)
    | Bshl | Blshr

  let pp_binop ppf = function
    | Band -> Fmt.pf ppf "bvand"
    | Bor -> Fmt.pf ppf "bvor"
    | Bxor -> Fmt.pf ppf "bvxor"
    | Badd -> Fmt.pf ppf "bvadd"
    | Bmul -> Fmt.pf ppf "bvmul"
    | Budiv -> Fmt.pf ppf "bvudiv"
    | Burem -> Fmt.pf ppf "bvurem"
    | Bshl -> Fmt.pf ppf "bvshl"
    | Blshr -> Fmt.pf ppf "bvlshr"

  let equal_binop op1 op2 =
    match op1, op2 with
    | Band, Band -> true
    | Band, _ | _, Band -> false

    | Bor, Bor -> true
    | Bor, _ | _, Bor -> false

    | Bxor, Bxor -> true
    | Bxor, _ | _, Bxor -> false

    | Badd, Badd -> true
    | Badd, _ | _, Badd -> false

    | Bmul, Bmul -> true
    | Bmul, _ | _, Bmul -> false

    | Budiv, Budiv -> true
    | Budiv, _ | _, Budiv -> false

    | Burem, Burem -> true
    | Burem, _ | _, Burem -> false

    | Bshl, Bshl -> true
    | Bshl, _ | _, Bshl -> false

    | Blshr, Blshr -> true

  let hash_binop : binop -> int = Hashtbl.hash

  let is_commutative = function
    | Band | Bor | Bxor | Badd | Bmul -> true
    | Budiv | Burem | Bshl | Blshr -> false

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

  type binrel = Rule | Rugt

  let pp_binrel ppf = function
    | Rule -> Fmt.pf ppf "bvule"
    | Rugt -> Fmt.pf ppf "bvugt"

  let equal_binrel : binrel -> binrel -> bool = Stdlib.(=)

  let hash_binrel : binrel -> int = Hashtbl.hash

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

  type view =
    | Cfun of X.r * fun_t
    | Crel of rel_t

  let pp_view ppf = function
    | Cfun (r, fn) ->
      Fmt.(pf ppf "%a =@ %a" (box X.print) r (box pp_fun_t) fn)
    | Crel rel ->
      pp_rel_t ppf rel

  let equal_view c1 c2 =
    match c1, c2 with
    | Cfun (r1, f1), Cfun (r2, f2) ->
      X.equal r1 r2 && equal_fun_t f1 f2
    | Cfun _, _ | _, Cfun _ -> false

    | Crel r1, Crel r2 ->
      equal_rel_t r1 r2

  let hash_view = function
    | Cfun (r, f) -> Hashtbl.hash (0, X.hash r, hash_fun_t f)
    | Crel r -> Hashtbl.hash (1, hash_rel_t r)

  let normalize_view = function
    | Cfun (r, f) -> Cfun (r, normalize_fun_t f)
    | Crel r -> Crel (normalize_rel_t r)

  type t = { view : view ; mutable tag : int }

  let view { view ; _ } = view

  let pp ppf { view; _ } = pp_view ppf view

  module W = Weak.Make(struct
      type nonrec t = t

      let equal c1 c2 = equal_view c1.view c2.view

      let hash c = hash_view c.view
    end)

  let hcons =
    let cnt = ref 0 in
    let tbl = W.create 17 in
    fun view ->
      let view = normalize_view view in
      let tagged = W.merge tbl { view ; tag = -1 } in
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
  let bvadd = cbinop Badd
  let bvsub r x y =
    (* r = x - y <-> x = r + y *)
    bvadd x r y
  let bvmul = cbinop Bmul
  let bvudiv = cbinop Budiv
  let bvurem = cbinop Burem
  let bvshl = cbinop Bshl
  let bvlshr = cbinop Blshr

  let crel r = hcons @@ Crel r

  let cbinrel op x y = crel (Rbinrel (op, x, y))

  let bvule = cbinrel Rule
  let bvugt = cbinrel Rugt

  let equal c1 c2 = c1.tag = c2.tag

  let hash c = Hashtbl.hash c.tag

  let compare c1 c2 = Int.compare c1.tag c2.tag

  let fold_args_fun_t f fn acc =
    match fn with
    | Fbinop (_, x, y) -> f y (f x acc)

  let fold_args_rel_t f r acc =
    match r with
    | Rbinrel (_op, x, y) -> f y (f x acc)

  let fold_args_view f c acc =
    match c with
    | Cfun (r, fn) -> fold_args_fun_t f fn (f r acc)
    | Crel r -> fold_args_rel_t f r acc

  let fold_args f c acc = fold_args_view f (view c) acc
end


module EC = ExplainedOrdered(struct
    include Constraint

    module Set = Set.Make(Constraint)
    module Map = Map.Make(Constraint)
  end)

module CompositeIntervalDomain = struct
  type var = X.r

  type atom = X.r

  type domain = Interval_domain.t

  let map_signed f { Bitv.value; negated } sz =
    if negated then Interval_domain.lognot sz (f value) else f value

  let map_domain f r =
    List.fold_left (fun ival { Bitv.bv; sz } ->
        let ival = Intervals.Int.scale Z.(~$1 lsl sz) ival in
        Intervals.Int.add ival @@
        match bv with
        | Bitv.Cte z -> Interval_domain.constant z
        | Other s -> map_signed f s sz
        | Ext (s, sz', i, j) ->
          Intervals.Int.extract (map_signed f s sz') ~ofs:i ~len:(j - i + 1)
      ) (Interval_domain.constant Z.zero) (Shostak.Bitv.embed r)
end

module XComposite = struct
  include Rel_utils.XComparable

  type atom = X.r

  let fold f r acc =
    List.fold_left (fun acc { Bitv.bv ; _ } ->
        match bv with
        | Bitv.Cte _ -> acc
        | Other { value ; _ } -> f value acc
        | Ext ({ value ; _ }, _, _, _) -> f value acc
      ) acc (Shostak.Bitv.embed r)
end

module XAtom = struct
  include Rel_utils.XComparable

  let type_info = X.type_info
end

module Interval_domains =
  Rel_utils.Domains_make
    (Interval_domain)
    (XAtom)
    (XComposite)
    (CompositeIntervalDomain)
    (BitvNormalForm)
    (EC)

module Interval_domains_uf =
  Rel_utils.UfHandle
    (Interval_domain)
    (Interval_domains.Ephemeral)

module Bitlist_domain = struct
  (* Note: these functions are not in [Bitlist] proper in order to avoid a
     (direct) dependency from [Bitlist] to the [Shostak] module. *)

  include Bitlist

  type constant = Z.t

  let constant n = exact n Ex.empty

  let filter_ty = is_bv_ty

  let unknown = function
    | Ty.Tbitv n -> extract unknown 0 n
    | _ ->
      (* Only bit-vector values can have bitlist domains. *)
      invalid_arg "unknown"

  let add_offset d cte =
    Bitlist.logor d (Bitlist.exact cte Explanation.empty)

  let sub_offset d cte =
    let cte = Bitlist.exact cte Explanation.empty in
    Bitlist.logand d (Bitlist.lognot cte)
end

module CompositeBitlistDomain = struct
  type var = X.r

  type atom = X.r

  type domain = Bitlist_domain.t

  let map_signed sz f { Bitv.value; negated } =
    let bl = f value in
    if negated then Bitlist.extract (Bitlist.lognot bl) 0 sz else bl

  let map_domain f r =
    List.fold_left (fun bl { Bitv.bv; sz } ->
        let open Bitlist in
        bl lsl sz lor
        match bv with
        | Bitv.Cte z -> extract (Bitlist_domain.constant z) 0 sz
        | Other r -> map_signed sz f r
        | Ext (r, r_sz, i, j) ->
          extract (map_signed r_sz f r) i (j - i + 1)
      ) (Bitlist_domain.constant Z.zero) (Shostak.Bitv.embed r)
end

module Bitlist_domains =
  Rel_utils.Domains_make
    (Bitlist_domain)
    (XAtom)
    (XComposite)
    (CompositeBitlistDomain)
    (BitvNormalForm)
    (EC)

module Bitlist_domains_uf =
  Rel_utils.UfHandle
    (Bitlist_domain)
    (Bitlist_domains.Ephemeral)

(** The ['c acts] type is used to register new facts and constraints in
    [Propagator.simplify]. *)
type 'c acts =
  { acts_add_lit_view : ex:Explanation.t -> X.r L.view -> unit
  (** Assert a semantic literal. *)
  ; acts_add_eq : ex:Explanation.t -> X.r -> X.r -> unit
  (** Assert equality between two semantic values. *)
  ; acts_add_constraint : ex:Explanation.t -> 'c -> unit
  (** Assert a new constraint. *)
  }

module Propagator : sig
  type t = Constraint.t
  (** The type of constraints.

      Constraints apply to semantic values of type [X.r] as arguments. *)

  val simplify : Uf.t -> t -> t acts -> bool
  (** [simplify c acts] simplifies the constraint [c] by calling appropriate
      functions on [acts].

      {b Note}: All the facts and constraints added through [acts] must be
      logically implied by [c] {b only}. Doing otherwise is a {b soundness bug}.

      Returns [true] if the constraint has been fully simplified and can
      be removed, and [false] otherwise.

      {b Note}: Returning [true] will cause the constraint to be removed, even
      if it was re-added with [acts_add_constraint]. If you want to add new
      facts/constraints but keep the existing constraint (usually a bad idea),
      return [false] instead. *)

  val propagate_bitlist : Bitlist_domains_uf.t -> ex:Ex.t -> t -> unit
  (** [propagate dom ~ex t] propagates the constraint [t] in domain [dom].

      The explanation [ex] justifies that the constraint [t] applies, and must
      be added to any domain that gets updated during propagation. *)

  val propagate_interval :
    Interval_domains_uf.t -> ex:Ex.t -> t -> unit
end = struct
  include Constraint

  let propagate_binop ~ex sz dx op dy dz =
    let norm bl = Bitlist.extract bl 0 sz in
    let open Rel_utils.HandleNotations(Bitlist_domain)(Bitlist_domains_uf) in
    match op with
    | Band ->
      update ~ex dx @@ norm @@ Bitlist.logand !!dy !!dz;
      (* Reverse propagation for y: if [x = y & z] then:
         - Any [1] in [x] must be a [1] in [y]
         - Any [0] in [x] that is also a [1] in [z] must be a [0] in [y]
      *)
      update ~ex dy @@ norm @@ Bitlist.ones !!dx;
      update ~ex dy @@ norm @@
      Bitlist.(logor (zeroes !!dx) (lognot (ones !!dz)));
      update ~ex dz @@ norm @@ Bitlist.ones !!dx;
      update ~ex dz @@ norm @@
      Bitlist.(logor (zeroes !!dx) (lognot (ones !!dy)))
    | Bor ->
      update ~ex dx @@ norm @@ Bitlist.logor !!dy !!dz;
      (* Reverse propagation for y: if [x = y | z] then:
         - Any [0] in [x] must be a [0] in [y]
         - Any [1] in [x] that is also a [0] in [z] must be a [1] in [y]
      *)
      update ~ex dy @@ norm @@ Bitlist.zeroes !!dx;
      update ~ex dy @@ norm @@
      Bitlist.(logand (ones !!dx) (lognot (zeroes !!dz)));
      update ~ex dz @@ norm @@ Bitlist.zeroes !!dx;
      update ~ex dz @@ norm @@
      Bitlist.(logand (ones !!dx) (lognot (zeroes !!dy)))
    | Bxor ->
      update ~ex dx @@ norm @@ Bitlist.logxor !!dy !!dz;
      (* x = y ^ z <-> y = x ^ z *)
      update ~ex dy @@ norm @@ Bitlist.logxor !!dx !!dz;
      update ~ex dz @@ norm @@ Bitlist.logxor !!dx !!dy
    | Badd ->
      update ~ex dx @@ norm @@ Bitlist.add !!dy !!dz;
      update ~ex dz @@ norm @@ Bitlist.sub !!dx !!dy;
      update ~ex dy @@ norm @@ Bitlist.sub !!dx !!dz

    | Bshl -> (* Only forward propagation for now *)
      update ~ex dx (Bitlist.bvshl ~size:sz !!dy !!dz)

    | Blshr -> (* Only forward propagation for now *)
      update ~ex dx (Bitlist.bvlshr ~size:sz !!dy !!dz)

    | Bmul -> (* Only forward propagation for now *)
      update ~ex dx @@ norm @@ Bitlist.mul !!dy !!dz

    | Budiv -> (* No bitlist propagation for now *)
      ()

    | Burem -> (* No bitlist propagation for now *)
      ()

  let propagate_interval_binop ~ex sz dr op dx dy =
    let open Rel_utils.HandleNotations(Interval_domain)(Interval_domains_uf) in
    let norm i = Intervals.Int.extract i ~ofs:0 ~len:sz in
    match op with
    | Badd ->
      update ~ex dr @@ norm @@ Intervals.Int.add !!dx !!dy;
      update ~ex dy @@ norm @@ Intervals.Int.sub !!dr !!dx;
      update ~ex dx @@ norm @@ Intervals.Int.sub !!dr !!dy

    | Bshl -> (* Only forward propagation for now *)
      update ~ex dr @@ Intervals.Int.bvshl ~size:sz !!dx !!dy

    | Blshr -> (* Only forward propagation for now *)
      update ~ex dr @@ Intervals.Int.lshr !!dx !!dy

    | Bmul -> (* Only forward propagation for now *)
      update ~ex dr @@ norm @@ Intervals.Int.mul !!dx !!dy

    | Budiv -> (* Only forward propagation for now *)
      update ~ex dr @@ Intervals.Int.bvudiv ~size:sz !!dx !!dy

    | Burem -> (* Only forward propagation for now *)
      update ~ex dr @@ Intervals.Int.bvurem !!dx !!dy

    | Band | Bor | Bxor ->
      (* No interval propagation for bitwise operators yet *)
      ()

  let propagate_fun_t ~ex dom r f =
    let get r = Bitlist_domains_uf.entry dom r in
    match f with
    | Fbinop (op, x, y) ->
      let n = bitwidth r in
      propagate_binop ~ex n (get r) op (get x) (get y)

  let propagate_interval_fun_t ~ex dom r f =
    let get r = Interval_domains_uf.entry dom r in
    match f with
    | Fbinop (op, x, y) ->
      let sz = bitwidth r in
      propagate_interval_binop ~ex sz (get r) op (get x) (get y)

  let propagate_binrel ~ex:_ _op _dx _dy =
    (* No bitlist propagation for relations yet *)
    ()

  let less_than_sup ~ex ~strict iv =
    let sup, ex' = Intervals.Int.upper_bound iv in
    let sup = if strict then Intervals.map_bound Z.pred sup else sup in
    Intervals.Int.of_bounds ~ex:(Ex.union ex ex') Unbounded sup

  let greater_than_inf ~ex ~strict iv =
    let inf, ex' = Intervals.Int.lower_bound iv in
    let inf = if strict then Intervals.map_bound Z.succ inf else inf in
    Intervals.Int.of_bounds ~ex:(Ex.union ex ex') inf  Unbounded

  let propagate_less_than ~ex ~strict dx dy =
    let open Rel_utils.HandleNotations(Interval_domain)(Interval_domains_uf) in
    (* Add justification prior to calling [update] to ensure that it is only
       stored on the appropriate bound. *)
    update ~ex:Ex.empty dx (less_than_sup ~ex ~strict !!dy);
    update ~ex:Ex.empty dy (greater_than_inf ~ex ~strict !!dx)

  let propagate_interval_binrel ~ex op dx dy =
    match op with
    | Rule ->
      propagate_less_than ~ex ~strict:false dx dy
    | Rugt ->
      propagate_less_than ~ex ~strict:true dy dx

  let propagate_rel_t ~ex dom r =
    let get r = Bitlist_domains_uf.entry dom r in
    match r with
    | Rbinrel (op, x, y) ->
      propagate_binrel ~ex op (get x) (get y)

  let propagate_interval_rel_t ~ex dom r =
    let get r = Interval_domains_uf.entry dom r in
    match r with
    | Rbinrel (op, x, y) ->
      propagate_interval_binrel ~ex op (get x) (get y)

  let propagate_view ~ex dom = function
    | Cfun (r, f) -> propagate_fun_t ~ex dom r f
    | Crel r -> propagate_rel_t ~ex dom r

  let propagate_interval_view ~ex dom = function
    | Cfun (r, f) -> propagate_interval_fun_t ~ex dom r f
    | Crel r -> propagate_interval_rel_t ~ex dom r

  let propagate_bitlist dom ~ex c =
    propagate_view ~ex dom (view c)

  let propagate_interval dom ~ex c =
    propagate_interval_view ~ex dom (view c)

  let cast ty n =
    match ty with
    | Ty.Tbitv sz -> const sz n
    | _ -> invalid_arg "cast"

  let value x =
    match Shostak.Bitv.embed x with
    | [ { bv = Cte n; _ } ] -> n
    | _ -> invalid_arg "const_value"

  (* Add the constraint: r = x *)
  let add_eq ~ex acts r x =
    acts.acts_add_eq ~ex r x

  (* Add the constraint: r = c *)
  let add_eq_const ~ex acts r c =
    add_eq ~ex acts r @@ const (bitwidth r) c

  (* Add the constraint: r = x & c *)
  let add_and_const ~ex acts r x c =
    (* TODO: apply to extractions for any [c]? Could be expensive for Shostak *)
    if Z.equal c Z.zero then (
      add_eq_const ~ex acts r Z.zero;
      true
    ) else if Z.equal c (Z.extract Z.minus_one 0 (bitwidth r)) then (
      add_eq ~ex acts r x;
      true
    ) else
      false

  (* Add the constraint: r = x | c *)
  let add_or_const ~ex acts r x c =
    (* TODO: apply to extractions for any [c]? Could be expensive for Shostak *)
    if Z.equal c Z.zero then (
      add_eq ~ex acts r x;
      true
    ) else if Z.equal c (Z.extract Z.minus_one 0 (bitwidth r)) then (
      add_eq_const ~ex acts r Z.minus_one;
      true
    ) else
      false

  (* Add the constraint: r = x ^ c *)
  let add_xor_const ~ex acts r x c =
    (* TODO: apply to extractions for any [c]? Could be expensive for Shostak *)
    if Z.equal c Z.zero then (
      add_eq ~ex acts r x;
      true
    ) else if Z.equal c (Z.extract Z.minus_one 0 (bitwidth r)) then (
      add_eq ~ex acts r
        (Shostak.Bitv.is_mine @@ Bitv.lognot @@ Shostak.Bitv.embed x);
      true
    ) else
      false

  (* Add the constraint: r = x + c *)
  let add_add_const ~ex acts r x c =
    let sz = bitwidth r in
    if Z.equal c Z.zero then (
      add_eq ~ex acts r x;
      true
    ) else if X.is_constant r then (
      (* c1 = x + c2 -> x = c1 - c2 *)
      add_eq_const ~ex acts x Z.(value r - c);
      true
    ) else if Z.testbit c (sz - 1) then
      (* Due to the modular nature of arithmetic on bit-vectors, [y = x + c]
         and [y = x + (2^sz - c)] are actually equivalent.

         We normalize to the version that uses a smaller constant. *)
      if Z.popcount c = 1 then
        (* INT_MIN (2^(sz - 1)) is special because -INT_MIN = INT_MIN and so
            r = x + INT_MIN
           and
            x = r + INT_MIN
           are actually equivalent, so we just pick a normalized order between x
           and r. *)
        if X.hash_cmp r x > 0 then (
          acts.acts_add_constraint ~ex (bvadd x r (const (bitwidth r) c));
          true
        ) else
          false
      else
        (* r = x - c -> x = r + c (mod 2^sz) *)
        let c = Z.neg @@ Z.signed_extract c 0 sz in
        assert (Z.sign c > 0 && not (Z.testbit c sz));
        acts.acts_add_constraint ~ex (bvadd x r (const sz c));
        true
    else
      false

  (* Add the constraint: r = x << c *)
  let add_shl_const ~ex acts r x c =
    let sz = bitwidth r in
    match Z.to_int c with
    | 0 -> add_eq ~ex acts r x
    | n when n < sz ->
      assert (n > 0);
      let r_bitv = Shostak.Bitv.embed r in
      let high_bits =
        Shostak.Bitv.is_mine @@
        Bitv.extract sz 0 (sz - 1 - n) (Shostak.Bitv.embed x)
      in
      add_eq ~ex acts
        (Shostak.Bitv.is_mine @@ Bitv.extract sz n (sz - 1) r_bitv)
        high_bits;
      add_eq_const ~ex acts
        (Shostak.Bitv.is_mine @@ Bitv.extract sz 0 (n - 1) r_bitv)
        Z.zero
    | _ | exception Z.Overflow ->
      add_eq_const ~ex acts r Z.zero

  (* Add the constraint: r = x * c *)
  let add_mul_const ~ex acts r x c =
    if Z.equal c Z.zero then (
      add_eq_const ~ex acts r Z.zero;
      true
    ) else if Z.popcount c = 1 then (
      let ofs = Z.numbits c - 1 in
      add_shl_const ~ex acts r x (Z.of_int ofs);
      true
    ) else
      false

  (* Add the constraint: r = x >> c *)
  let add_lshr_const ~ex acts r x c =
    let sz = bitwidth r in
    match Z.to_int c with
    | 0 -> add_eq ~ex acts r x
    | n when n < sz ->
      assert (n > 0);
      let r_bitv = Shostak.Bitv.embed r in
      let low_bits =
        Shostak.Bitv.is_mine @@
        Bitv.extract sz n (sz - 1) (Shostak.Bitv.embed x)
      in
      add_eq ~ex acts
        (Shostak.Bitv.is_mine @@ Bitv.extract sz 0 (sz - 1 - n) r_bitv)
        low_bits;
      add_eq_const ~ex acts
        (Shostak.Bitv.is_mine @@ Bitv.extract sz (sz - n) (sz - 1) r_bitv)
        Z.zero
    | _ | exception Z.Overflow ->
      add_eq_const ~ex acts r Z.zero

  (* Ground evaluation rules for binary operators. *)
  let eval_binop op ty x y =
    match op with
    | Band -> cast ty @@ Z.logand x y
    | Bor -> cast ty @@ Z.logor x y
    | Bxor -> cast ty @@ Z.logxor x y
    | Badd -> cast ty @@ Z.add x y
    | Bmul -> cast ty @@ Z.mul x y
    | Budiv ->
      if Z.equal y Z.zero then
        cast ty Z.minus_one
      else
        cast ty @@ Z.div x y
    | Burem ->
      if Z.equal y Z.zero then
        cast ty x
      else
        cast ty @@ Z.rem x y
    | Bshl -> (
        match ty, Z.to_int y with
        | Tbitv sz, y when y < sz ->
          cast ty @@ Z.shift_left x y
        | _ | exception Z.Overflow -> cast ty Z.zero
      )
    | Blshr -> (
        match ty, Z.to_int y with
        | Tbitv sz, y when y < sz ->
          cast ty @@ Z.shift_right x y
        | _ | exception Z.Overflow -> cast ty Z.zero
      )

  (* Constant simplification rules for binary operators.

     The case where all arguments are constant and the function can be fully
     evaluated is assumed to be dealt with prior to calling this function.

     Algebraic rules (e.g. x & x = x) are in [rw_binop_algebraic].*)
  let rw_binop_const ~ex acts op r x y =
    (* NB: for commutative operators, arguments are sorted, so the second
       argument can only be constant if the first argument also is constant. *)
    match op with
    | Band when X.is_constant x ->
      add_and_const ~ex acts r y (value x)
    | Band when X.is_constant y ->
      add_and_const ~ex acts r x (value y)
    | Band -> false

    | Bor when X.is_constant x ->
      add_or_const ~ex acts r y (value x)
    | Bor when X.is_constant y ->
      add_or_const ~ex acts r x (value y)
    | Bor -> false

    | Bxor when X.is_constant x ->
      add_xor_const ~ex acts r y (value x)
    | Bxor when X.is_constant y ->
      add_xor_const ~ex acts r x (value y)
    | Bxor when X.is_constant r ->
      add_xor_const ~ex acts x y (value r)
    | Bxor -> false

    | Badd when X.is_constant x ->
      add_add_const ~ex acts r y (value x)
    | Badd when X.is_constant y ->
      add_add_const ~ex acts r x (value y)
    | Badd ->
      false

    | Bmul when X.is_constant x ->
      add_mul_const ~ex acts r y (value x)
    | Bmul when X.is_constant y ->
      add_mul_const ~ex acts r x (value y)
    | Bmul -> false

    | Budiv | Burem -> false

    (* shifts becomes a simple extraction when we know the right-hand side *)
    | Bshl when X.is_constant y ->
      add_shl_const ~ex acts r x (value y);
      true
    | Bshl -> false

    | Blshr when X.is_constant y ->
      add_lshr_const ~ex acts r x (value y);
      true
    | Blshr -> false

  (* Algebraic rewrite rules for binary operators.

     Rules based on constant simplifications are in [rw_binop_const]. *)
  let rw_binop_algebraic ~ex acts op r x y =
    match op with
    (* x & x = x ; x | x = x *)
    | Band | Bor when X.equal x y ->
      add_eq ~ex acts r x; true

    (* r ^ x ^ x = 0 <-> r = 0 *)
    | Bxor when X.equal x y ->
      add_eq_const ~ex acts r Z.zero; true
    | Bxor when X.equal r x ->
      add_eq_const ~ex acts y Z.zero; true
    | Bxor when X.equal r y ->
      add_eq_const ~ex acts x Z.zero; true

    | Badd when X.equal x y ->
      (* r = x + x -> r = 2x -> r = x << 1 *)
      add_shl_const ~ex acts r x Z.one; true
    | Badd when X.equal r x ->
      (* x = x + y -> y = 0 *)
      add_eq_const ~ex acts y Z.zero; true
    | Badd when X.equal r y ->
      (* y = x + y -> x = 0 *)
      add_eq_const ~ex acts x Z.zero; true

    | _ -> false

  let simplify_binop ~ex acts op r x y =
    if X.is_constant x && X.is_constant y then (
      add_eq ~ex acts r @@
      eval_binop op (X.type_info r) (value x) (value y);
      true
    ) else
      rw_binop_const ~ex acts op r x y ||
      rw_binop_algebraic ~ex acts op r x y

  let simplify_fun_t uf acts r = function
    | Fbinop (op, x, y) ->
      let r, ex_r = Uf.find_r uf r in
      let x, ex_x = Uf.find_r uf x in
      let y, ex_y = Uf.find_r uf y in
      let ex = Explanation.union ex_r (Explanation.union ex_x ex_y) in
      simplify_binop ~ex acts op r x y

  let simplify_binrel ~ex acts op x y =
    match op with
    | Rugt when X.equal x y ->
      acts.acts_add_eq ~ex X.top X.bot;
      true
    | Rule | Rugt -> false

  let simplify_rel_t uf acts = function
    | Rbinrel (op, x, y) ->
      let x, ex_x = Uf.find_r uf x in
      let y, ex_y = Uf.find_r uf y in
      simplify_binrel ~ex:(Explanation.union ex_x ex_y) acts op x y

  let simplify_view uf acts = function
    | Cfun (r, f) -> simplify_fun_t uf acts r f
    | Crel r -> simplify_rel_t uf acts r

  let simplify uf c acts =
    simplify_view uf acts (view c)
end

let extract_binop =
  let open Constraint in function
    | Sy.BVand -> Some bvand
    | BVor -> Some bvor
    | BVxor -> Some bvxor
    | BVadd -> Some bvadd
    | BVsub -> Some bvsub
    | BVmul -> Some bvmul
    | BVudiv -> Some bvudiv
    | BVurem -> Some bvurem
    | BVshl -> Some bvshl
    | BVlshr -> Some bvlshr
    | _ -> None

let extract_term r terms =
  if X.is_a_leaf r then SX.add r terms
  else terms

let extract_constraints terms domain int_domain uf r t =
  match E.term_view t with
  | { f = Op op; xs = [ x; y ]; _ } -> (
      match extract_binop op with
      | Some mk ->
        let rx, exx = Uf.find uf x
        and ry, exy = Uf.find uf y in
        let c = mk r rx ry in
        let ex = Ex.union exx exy in
        let domain =
          Bitlist_domains.watch (explained ~ex c) rx @@
          Bitlist_domains.watch (explained ~ex c) ry @@
          domain
        in
        let int_domain =
          Interval_domains.watch (explained ~ex c) rx @@
          Interval_domains.watch (explained ~ex c) ry @@
          int_domain
        in
        terms, domain, int_domain
      | None -> extract_term r terms, domain, int_domain
    )
  | _ -> extract_term r terms, domain, int_domain

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
        "bitlist propagated: %a = %a%a" X.print lhs X.print rhs Ex.print ex;
    (Uf.LX.mkv_eq lhs rhs , ex) ::
    if sz = w then [] else
      mk_eq ex rest (w - sz) (Z.extract z 0 (w - sz))

(** [add_eqs acc r bl], where [r] is a semantic value and [bl] is a bitlist that
    applies to [r], exposes the equality [r = bl] as a list of Xliteral values
    (accumulated into [acc]) so that the union-find learns about the equality *)
let add_eqs =
  let rec aux x x_sz acc width bl =
    let known = Z.lognot (Bitlist.unknown_bits bl) in
    let known = Z.extract known 0 width in
    let nbits = Z.numbits known in
    assert (nbits <= width);
    if nbits = 0 then
      acc
    else if nbits < width then
      aux x x_sz acc nbits (Bitlist.extract bl 0 nbits)
    else
      let nbits = Z.numbits (Z.extract (Z.lognot known) 0 width) in
      let v = Z.extract (Bitlist.value bl) nbits (width - nbits) in
      assert (nbits < width);
      let extracted = Bitv.extract x_sz nbits (width - 1) x in
      let lits = mk_eq (Bitlist.explanation bl) extracted (width - nbits) v in
      if nbits = 0 then
        lits @ acc
      else
        aux x x_sz (lits @ acc) nbits (Bitlist.extract bl 0 nbits)
  in
  fun acc x x_sz bl ->
    aux x x_sz acc x_sz bl

module Any_constraint = struct
  type t =
    | Constraint of Constraint.t explained
    | Structural of X.r
    (** Structural constraint associated with [X.r]. See
        {!Rel_utils.Bitlist_domains.structural_propagation}. *)

  let equal a b =
    match a, b with
    | Constraint ca, Constraint cb -> Constraint.equal ca.value cb.value
    | Constraint _, Structural _ | Structural _, Constraint _ -> false
    | Structural xa, Structural xb -> X.equal xa xb

  let hash = function
    | Constraint c -> 2 * Constraint.hash c.value
    | Structural r -> 2 * X.hash r + 1

  let propagate constraint_propagate structural_propagation c =
    Steps.incr CP;
    match c with
    | Constraint { value; explanation = ex } ->
      constraint_propagate ~ex value
    | Structural r ->
      structural_propagation r
end

module QC = Uqueue.Make(Any_constraint)

let propagate_queue queue constraint_propagate structural_propagation =
  try
    while true do
      Any_constraint.propagate
        constraint_propagate
        structural_propagation
        (QC.pop queue)
    done
  with QC.Empty -> ()

let finite_lower_bound = function
  | Intervals_intf.Unbounded -> Z.zero
  | Closed n -> n
  | Open n -> Z.succ n

let finite_upper_bound ~size:sz = function
  | Intervals_intf.Unbounded -> Z.extract Z.minus_one 0 sz
  | Closed n -> n
  | Open n -> Z.pred n

(* If m and M are the minimal and maximal values of an union of intervals, the
   longest sequence of most significant bits shared between m and M can be fixed
   in the bit-vector domain; see "Is to BVs" in section 4.1 of

   Sharpening Constraint Programming approaches for Bit-Vector Theory.
   Zakaria Chihani, Bruno Marre, François Bobot, Sébastien Bardin.
   CPAIOR 2017. International Conference on AI and OR Techniques in
   Constraint Programming for Combinatorial Optimization Problems, Jun
   2017, Padova, Italy.
   https://cea.hal.science/cea-01795779/document

   Relevant excerpt:

   For example, m = 48 and M = 52 (00110000 and 00110100 in binary) share their
   five most-significant bits, denoted [00110???]. Therefore, a bit-vector bl =
   [0??1???0] can be refined into [00110??0]. *)
let constrain_bitlist_from_interval ~size:sz bv int =
  let
    open Rel_utils.HandleNotations(Bitlist_domain)(Bitlist_domains.Ephemeral)
  in
  let inf, inf_ex = Intervals.Int.lower_bound int in
  let inf = finite_lower_bound inf in
  let sup, sup_ex = Intervals.Int.upper_bound int in
  let sup = finite_upper_bound ~size:sz sup in

  let distinct = Z.logxor inf sup in
  (* If [distinct] is negative, [inf] and [sup] have different signs and there
     are no significant shared bits. *)
  if Z.sign distinct >= 0 then
    let ofs = Z.numbits distinct in
    update ~ex:Ex.empty bv @@
    Bitlist.(
      exact Z.((inf asr ofs) lsl ofs) (Ex.union inf_ex sup_ex) lor
      extract unknown 0 ofs
    )

(* Algorithm 1 from

   Sharpening Constraint Programming approaches for Bit-Vector Theory.
   Zakaria Chihani, Bruno Marre, François Bobot, Sébastien Bardin.
   CPAIOR 2017. International Conference on AI and OR Techniques in
   Constraint Programming for Combinatorial Optimization Problems, Jun
   2017, Padova, Italy.
   https://cea.hal.science/cea-01795779/document

   This function is a wrapper calling [Bitlist.increase_lower_bound] and
   [Bitlist.decrease_upper_bound] on all the constituent intervals of an union;
   see the documentation of these functions for details. *)
let constrain_interval_from_bitlist ~size:sz int bv =
  let
    open Rel_utils.HandleNotations(Interval_domain)(Interval_domains.Ephemeral)
  in
  let ex = Bitlist.explanation bv in
  (* Handy wrapper around [of_complement] *)
  let remove ~ex i2 i1 =
    match Intervals.Int.of_complement ~ex i1 with
    | Empty _ -> invalid_arg "remove"
    | NonEmpty i1 ->
      match Intervals.Int.intersect i2 i1 with
      | NonEmpty i -> i
      | Empty ex ->
        raise @@ Interval_domains.Inconsistent ex
  in
  update ~ex int @@
  Intervals.Int.fold (fun acc i ->
      let { Intervals_intf.lb ; ub } = Intervals.Int.Interval.view i in
      let lb = finite_lower_bound lb in
      let ub = finite_upper_bound ~size:sz ub in
      let acc =
        match Bitlist.increase_lower_bound bv lb with
        | new_lb when Z.compare new_lb lb > 0 ->
          (* lower bound increased; remove [lb, new_lb[ *)
          remove ~ex acc
          @@ Intervals.Int.Interval.of_bounds (Closed lb) (Open new_lb)
        | new_lb ->
          (* no change *)
          assert (Z.equal new_lb lb);
          acc
        | exception Not_found ->
          (* No value larger than lb matches the bit-pattern *)
          remove ~ex acc
          @@ Intervals.Int.Interval.of_bounds (Closed lb) Unbounded
      in
      let acc =
        match Bitlist.decrease_upper_bound bv ub with
        | new_ub when Z.compare new_ub ub < 0 ->
          (* upper bound decreased; remove ]new_ub, ub] *)
          remove ~ex acc
          @@ Intervals.Int.Interval.of_bounds (Open new_ub) (Closed ub)
        | new_ub ->
          (* no change *)
          assert (Z.equal new_ub ub);
          acc
        | exception Not_found ->
          (* No value smaller than ub matches the bit-pattern *)
          remove ~ex acc
          @@ Intervals.Int.Interval.of_bounds Unbounded (Closed ub)
      in
      acc
    ) !!int !!int

let iter_parents a f t =
  match Rel_utils.XComparable.Map.find a t with
  | cs -> Rel_utils.XComparable.Set.iter f cs
  | exception Not_found -> ()

let propagate_bitlist queue vars dom =
  let structural_propagation r =
    let open Rel_utils.HandleNotations(Bitlist_domain)(Bitlist_domains_uf) in
    let get r = !!(Bitlist_domains_uf.entry dom r) in
    let update r d =
      update ~ex:Explanation.empty (Bitlist_domains_uf.entry dom r) d
    in
    if X.is_a_leaf r then
      iter_parents r (fun p ->
          if X.is_a_leaf p then
            assert (X.equal r p)
          else
            update p (CompositeBitlistDomain.map_domain get p)
        ) vars
    else
      let iter_signed sz f { Bitv.value; negated } bl =
        let bl = if negated then Bitlist.(extract (lognot bl)) 0 sz else bl in
        f value bl
      in
      ignore @@ List.fold_left (fun (bl, w) { Bitv.bv; sz } ->
          (* Extract the bitlist associated with the current component *)
          let mid = w - sz in
          let bl_tail = Bitlist.extract bl 0 mid in
          let bl = Bitlist.extract bl mid (w - mid) in

          match bv with
          | Bitv.Cte z ->
            assert (Z.numbits z <= sz);
            (* Nothing to update, but still check for consistency! *)
            ignore @@ Bitlist.intersect bl (Bitlist.exact z Ex.empty);
            bl_tail, mid
          | Other r ->
            iter_signed sz update r bl;
            (bl_tail, mid)
          | Ext (r, r_size, i, j) ->
            (* r<i, j> = bl -> r = ?^(r_size - j - 1) @ bl @ ?^i *)
            assert (i + r_size - j - 1 + w - mid = r_size);
            let hi = Bitlist.(extract unknown 0 (r_size - j - 1)) in
            let lo = Bitlist.(extract unknown 0 i) in
            let bl_hd = Bitlist.((hi lsl (j + 1)) lor (bl lsl i) lor lo) in
            iter_signed r_size update r bl_hd;
            (bl_tail, mid)
        ) ((get r), (bitwidth r)) (Shostak.Bitv.embed r)
  in
  propagate_queue
    queue
    (Propagator.propagate_bitlist dom)
    structural_propagation

let propagate_intervals queue vars dom =
  let structural_propagation r =
    let open Rel_utils.HandleNotations(Interval_domain)(Interval_domains_uf) in
    let get r = !!(Interval_domains_uf.entry dom r) in
    let update r d =
      update ~ex:Explanation.empty (Interval_domains_uf.entry dom r) d
    in
    if X.is_a_leaf r then
      iter_parents r (fun p ->
          if X.is_a_leaf p then
            assert (X.equal r p)
          else
            update p (CompositeIntervalDomain.map_domain get p)
        ) vars
    else
      let iter_signed f { Bitv.value; negated } sz int =
        f value (if negated then Interval_domain.lognot sz int else int)
      in
      let int = get r in
      let width = bitwidth r in
      let j =
        List.fold_left (fun j { Bitv.bv; sz } ->
            (* sz = j - i + 1 => i = j - sz + 1 *)
            let int = Intervals.Int.extract int ~ofs:(j - sz + 1) ~len:sz in

            begin match bv with
              | Bitv.Cte z ->
                (* Nothing to update, but still check for consistency *)
                ignore @@
                Interval_domain.intersect int (Interval_domain.constant z)
              | Other s -> iter_signed update s sz int
              | Ext (r, r_size, i, j) ->
                (* r<i, j> = bl -> r = ?^(r_size - j - 1) @ bl @ ?^i *)
                assert (i + r_size - j - 1 + sz = r_size);
                let lo = Interval_domain.unknown (Tbitv i) in
                let int = Intervals.Int.scale Z.(~$1 lsl i) int in
                let hi = Interval_domain.unknown (Tbitv (r_size - j - 1)) in
                let hi =
                  Intervals.Int.scale Z.(~$1 lsl Stdlib.(i + sz)) hi
                in
                iter_signed update r r_size Intervals.Int.(add hi (add int lo))
            end;

            (j - sz)
          ) (width - 1) (Shostak.Bitv.embed r)
      in
      assert (j = -1)
  in
  propagate_queue
    queue
    (Propagator.propagate_interval dom)
    structural_propagation

module HC = Hashtbl.Make(Constraint)

let simplify_all uf eqs touched (dom, idom) =
  let eqs = ref eqs in
  let to_add = HC.create 17 in
  let simplify c c_ex (dom, idom) =
    let acts_add_lit_view ~ex l =
      eqs := (l, Explanation.union ex c_ex) :: !eqs
    in
    let acts_add_eq ~ex u v =
      acts_add_lit_view ~ex (Uf.LX.mkv_eq u v)
    in
    let acts_add_constraint ~ex c =
      let c = explained ~ex:(Explanation.union ex c_ex) c in
      HC.replace to_add c.value c.explanation
    in
    let acts =
      { acts_add_lit_view
      ; acts_add_eq
      ; acts_add_constraint } in
    if Propagator.simplify uf c acts then
      let c = explained ~ex:c_ex c in
      (Bitlist_domains.unwatch c dom, Interval_domains.unwatch c idom)
    else
      (dom, idom)
  in
  let dom, idom = HC.fold simplify touched (dom, idom) in
  !eqs,
  HC.fold (fun c c_ex (dom, idom) ->
      let c = explained ~ex:c_ex c in
      Constraint.fold_args (fun r (dom, idom) ->
          let r, _ = Uf.find_r uf r in
          Bitlist_domains.watch c r dom,
          Interval_domains.watch c r idom
        ) c.value (dom, idom)
    ) to_add (dom, idom)

let rec propagate_all uf eqs bdom idom =
  (* Optimization to avoid unnecessary allocations *)
  let do_bitlist = Bitlist_domains.needs_propagation bdom in
  let do_intervals = Interval_domains.needs_propagation idom in
  let do_any = do_bitlist || do_intervals in
  if do_any then
    let shostak_candidates = HX.create 17 in
    let seen_constraints = HC.create 17 in
    let bitlist_queue = QC.create 17 in
    let interval_queue = QC.create 17 in
    let touch_c queue c =
      HC.replace seen_constraints c.value c.explanation;
      QC.push queue (Constraint c)
    in
    let touch tbl queue r =
      HX.replace tbl r ();
      QC.push queue (Structural r)
    in
    let bitlist_changed = HX.create 17 in
    let interval_changed = HX.create 17 in
    let bitlist_events =
      { Rel_utils.evt_atomic_change = touch bitlist_changed bitlist_queue
      ; evt_composite_change = touch bitlist_changed bitlist_queue
      ; evt_watch_trigger = touch_c bitlist_queue }
    and interval_events =
      { Rel_utils.evt_atomic_change = touch interval_changed interval_queue
      ; evt_composite_change = touch interval_changed interval_queue
      ; evt_watch_trigger = touch_c interval_queue }
    in
    let bvars = Bitlist_domains.parents bdom in
    let ivars = Interval_domains.parents idom in

    let bdom = Bitlist_domains.edit ~events:bitlist_events bdom in
    let idom = Interval_domains.edit ~events:interval_events idom in

    let uf_bdom = Bitlist_domains_uf.wrap uf bdom in
    let uf_idom = Interval_domains_uf.wrap uf idom in

    (* First, we propagate the pending constraints to both domains. Changes in
       the bitlist domain are used to shrink the interval domains. *)
    propagate_bitlist bitlist_queue bvars uf_bdom;
    assert (QC.is_empty bitlist_queue);

    HX.iter (fun r () ->
        HX.replace shostak_candidates r ();
        constrain_interval_from_bitlist ~size:(bitwidth r)
          Interval_domains.Ephemeral.(entry idom r)
          Bitlist_domains.Ephemeral.(Entry.domain (entry bdom r))
      ) bitlist_changed;
    HX.clear bitlist_changed;
    propagate_intervals interval_queue ivars uf_idom;
    assert (QC.is_empty interval_queue);

    (* Now the interval domain is stable, but the new intervals may have an
       impact on the bitlist domains, so we must shrink them again when
       applicable. We repeat until a fixpoint is reached. *)
    while HX.length interval_changed > 0 do
      HX.iter (fun r () ->
          constrain_bitlist_from_interval ~size:(bitwidth r)
            Bitlist_domains.Ephemeral.(entry bdom r)
            Interval_domains.Ephemeral.(Entry.domain (entry idom r))
        ) interval_changed;
      HX.clear interval_changed;
      propagate_bitlist bitlist_queue bvars uf_bdom;
      assert (QC.is_empty bitlist_queue);

      HX.iter (fun r () ->
          HX.replace shostak_candidates r ();
          constrain_interval_from_bitlist ~size:(bitwidth r)
            Interval_domains.Ephemeral.(entry idom r)
            Bitlist_domains.Ephemeral.(Entry.domain (entry bdom r))
        ) bitlist_changed;
      HX.clear bitlist_changed;
      propagate_intervals interval_queue ivars uf_idom;
      assert (QC.is_empty interval_queue);
    done;

    let eqs =
      HX.fold (fun r () acc ->
          let d = Bitlist_domains.Ephemeral.(Entry.domain (entry bdom r)) in
          add_eqs acc (Shostak.Bitv.embed r) (bitwidth r) d
        ) shostak_candidates eqs
    in

    let bdom, idom =
      Bitlist_domains.snapshot bdom, Interval_domains.snapshot idom
    in
    let eqs, (bdom, idom) = simplify_all uf eqs seen_constraints (bdom, idom) in

    (* Propagate again in case constraints were simplified. *)
    propagate_all uf eqs bdom idom
  else
    eqs, bdom, idom

type t =
  { delayed : Rel_utils.Delayed.t
  ; terms : SX.t
  ; size_splits : Q.t }

let empty uf =
  { delayed = Rel_utils.Delayed.create ~is_ready:X.is_constant dispatch
  ; terms = SX.empty
  ; size_splits = Q.one },
  Uf.GlobalDomains.add (module Bitlist_domains) Bitlist_domains.empty @@
  Uf.GlobalDomains.add (module Interval_domains) Interval_domains.empty @@
  Uf.domains uf

let assume env uf la =
  let ds = Uf.domains uf in
  let domain = Uf.GlobalDomains.find (module Bitlist_domains) ds in
  let int_domain =
    Uf.GlobalDomains.find (module Interval_domains) ds
  in
  let delayed, result = Rel_utils.Delayed.assume env.delayed uf la in
  let (domain, int_domain, eqs, size_splits) =
    try
      let (domain, int_domain, eqs, size_splits) =
        List.fold_left
          (fun (domain, int_domain, eqs, ss) (a, _root, ex, orig) ->
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
             | L.Builtin (is_true, BVULE, [x; y]), _ ->
               let x, exx = Uf.find_r uf x in
               let y, exy = Uf.find_r uf y in
               let ex = Ex.union ex @@ Ex.union exx exy in
               let c =
                 if is_true then
                   Constraint.bvule x y
                 else
                   Constraint.bvugt x y
               in
               (* Only watch comparisons on the interval domain since we don't
                  propagate them in the bitlist domain. . *)
               let int_domain =
                 Interval_domains.watch (explained ~ex c) x @@
                 Interval_domains.watch (explained ~ex c) y @@
                 int_domain
               in
               (domain, int_domain, eqs, ss)
             | L.Distinct (false, [rr; nrr]), _ when is_1bit rr ->
               (* We don't (yet) support [distinct] in general, but we must
                  support it for case splits to avoid looping.

                  We are a bit more general and support it for 1-bit vectors,
                  for which `distinct` can be expressed using `bvnot`. *)
               let not_nrr =
                 Shostak.Bitv.is_mine (Bitv.lognot (Shostak.Bitv.embed nrr))
               in
               (domain, int_domain, (Uf.LX.mkv_eq rr not_nrr, ex) :: eqs, ss)
             | _ -> (domain, int_domain, eqs, ss)
          )
          (domain, int_domain, [], env.size_splits)
          la
      in
      let eqs, domain, int_domain = propagate_all uf eqs domain int_domain in
      if Options.get_debug_bitv () && not (Compat.List.is_empty eqs) then (
        Printer.print_dbg
          ~module_name:"Bitv_rel" ~function_name:"assume"
          "bitlist domain: @[%a@]" Bitlist_domains.pp domain;
        Printer.print_dbg
          ~module_name:"Bitv_rel" ~function_name:"assume"
          "interval domain: @[%a@]" Interval_domains.pp int_domain;
      );
      (domain, int_domain, eqs, size_splits)
    with Bitlist.Inconsistent ex | Interval_domain.Inconsistent ex ->
      raise @@ Ex.Inconsistent (ex, Uf.cl_extract uf)
  in
  let assume =
    List.rev_map (fun (lit, ex) -> Literal.LSem lit, ex, Th_util.Other) eqs
  in
  let result =
    { result with assume = List.rev_append assume result.assume }
  in
  { delayed ; size_splits ; terms = env.terms },
  Uf.GlobalDomains.add (module Bitlist_domains) domain @@
  Uf.GlobalDomains.add (module Interval_domains) int_domain ds,
  result

let query _ _ _ = None

let case_split env uf ~for_model =
  if not for_model && Stdlib.(env.size_splits >= Options.get_max_split ()) then
    []
  else
    let domain =
      Uf.GlobalDomains.find (module Bitlist_domains) (Uf.domains uf)
    in
    (* Look for representatives with minimal, non-fully known, domain size.

       We first look among the constrained variables, then if there are no
       constrained variables, all the remaining variables.

       [nunk] is the number of unknown bits. *)
    let f_acc r acc =
      let r, _ = Uf.find_r uf r in
      let bl = Bitlist_domains.get r domain in
      let nunk = Z.popcount (Bitlist.unknown_bits bl) in
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
      match SX.fold f_acc env.terms None with
      | Some (nunk, xs) -> nunk, xs
      | None -> 0, SX.empty
    in
    (* For now, just pick a value for the most significant bit. *)
    match SX.choose candidates with
    | r ->
      let rr, _ = Uf.find_r uf r in
      let bl = Bitlist_domains.get rr domain in
      let r =
        let es = Uf.rclass_of uf r in
        try Uf.make uf (Expr.Set.choose es)
        with Not_found -> r
      in
      let w = bitwidth r in
      let unknown = Z.extract (Bitlist.unknown_bits bl) 0 w in
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
  let ds = Uf.domains uf in
  let delayed, eqs = Rel_utils.Delayed.add env.delayed uf r t in
  let env, ds, eqs =
    if is_bv_r r then
      let dom = Uf.GlobalDomains.find (module Bitlist_domains) ds in
      let idom = Uf.GlobalDomains.find (module Interval_domains) ds in
      let terms, dom, idom = extract_constraints env.terms dom idom uf r t in
      { env with terms },
      Uf.GlobalDomains.add (module Bitlist_domains) dom @@
      Uf.GlobalDomains.add (module Interval_domains) idom @@
      ds,
      eqs
    else
      env, ds, eqs
  in
  { env with delayed }, ds, eqs

let optimizing_objective _env uf Objective.Function.{ e; is_max; _ } =
  let ty = E.type_info e in
  if not (is_bv_ty ty) then None
  else
    let r = Uf.make uf e in
    let rr, _ = Uf.find_r uf r in
    match Shostak.Bitv.embed rr with
    | [ { bv = Cte n ; sz }] ->
      if Options.get_debug_optimize () then
        Printer.print_dbg "%a has the value %a@."
          E.print e
          Z.pp_print n;

      let value = Objective.Value.Value (E.BV.of_Z ~size:sz n) in
      let case_split =
        Uf.LX.mkv_eq r rr, true, Th_util.CS (Th_util.Th_bitv, Q.one)
      in
      Some Th_util.{ value ; case_split }
    | _ ->
      let ds = Uf.domains uf in
      let int_domains = Uf.GlobalDomains.find (module Interval_domains) ds in
      let int = Interval_domains.get rr int_domains in
      let sz = bitwidth rr in
      let value_z =
        if is_max then
          finite_upper_bound ~size:sz @@
          fst (Intervals.Int.upper_bound int)
        else
          finite_lower_bound @@
          fst (Intervals.Int.lower_bound int)
      in
      let value = Objective.Value.Value (E.BV.of_Z ~size:sz value_z) in
      let lit = Uf.LX.mkv_eq r (const sz value_z) in
      let case_split = lit, true, Th_util.CS (Th_util.Th_bitv, Q.one) in
      Some { value ; case_split }

let new_terms _ = Expr.Set.empty

let instantiate ~do_syntactic_matching:_ _ env _ _ = env, []

let assume_th_elt t th_elt _ =
  match th_elt.Expr.extends with
  | Util.Bitv ->
    failwith "This Theory does not support theories extension"
  | _ -> t

module Test = struct
  let shared_msb sz inf sup =
    sz - Z.numbits (Z.logxor inf sup)
end
