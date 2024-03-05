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

  let map_signed f { Bitv.value; negated } t =
    let bl = f value t in
    if negated then lognot bl else bl

  let map_leaves f r acc =
    List.fold_left (fun bl { Bitv.bv; sz } ->
        concat bl @@
        match bv with
        | Bitv.Cte z -> exact sz z Ex.empty
        | Other r -> map_signed f r acc
        | Ext (r, _r_size, i, j) -> extract (map_signed f r acc) i j
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

  val propagate : ex:Ex.t -> t -> Domains.Ephemeral.t -> unit
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
    | Band _, _
    | Bor _, _
    | Bxor _, _ -> false

  let hash_repr = function
    | Band (x, y, z) -> Hashtbl.hash (0, X.hash x, X.hash y, X.hash z)
    | Bor (x, y, z) -> Hashtbl.hash (1, X.hash x, X.hash y, X.hash z)
    | Bxor xs ->
      Hashtbl.hash (2, SX.fold (fun r acc -> X.hash r :: acc) xs [])

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

  let pp ppf { repr; _ } = pp_repr ppf repr

  let compare { tag = t1; _ } { tag = t2; _ } = Stdlib.compare t1 t2

  let equal t1 t2 = Int.equal t1.tag t2.tag

  let hash t1 = Hashtbl.hash t1.tag

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

  let propagate ~ex { repr; _ } dom =
    let open Domains.Ephemeral in
    let get r = handle dom r in
    Steps.incr CP;
    match repr with
    | Band (x, y, z) ->
      let dx = get x and dy = get y and dz = get z in
      update ~ex dx (Bitlist.logand !!dy !!dz);
      (* Reverse propagation for y: if [x = y & z] then:
         - Any [1] in [x] must be a [1] in [y]
         - Any [0] in [x] that is also a [1] in [z] must be a [0] in [y]
      *)
      update ~ex dy (Bitlist.ones !!dx);
      update ~ex dy Bitlist.(logor (zeroes !!dx) (lognot (ones !!dz)));
      update ~ex dz (Bitlist.ones !!dx);
      update ~ex dz Bitlist.(logor (zeroes !!dx) (lognot (ones !!dy)))
    | Bor (x, y, z) ->
      let dx = get x and dy = get y and dz = get z in
      update ~ex dx (Bitlist.logor !!dy !!dz);
      (* Reverse propagation for y: if [x = y | z] then:
         - Any [0] in [x] must be a [0] in [y]
         - Any [1] in [x] that is also a [0] in [z] must be a [1] in [y]
      *)
      update ~ex dy (Bitlist.zeroes !!dx);
      update ~ex dy Bitlist.(logand (ones !!dx) (lognot (zeroes !!dz)));
      update ~ex dz (Bitlist.zeroes !!dx);
      update ~ex dz Bitlist.(logand (ones !!dx) (lognot (zeroes !!dy)))
    | Bxor xs ->
      SX.iter (fun x ->
          let dx = get x in
          let dx' =
            SX.fold (fun y acc ->
                if X.equal x y then
                  acc
                else
                  Bitlist.logxor !!(get y) acc
              ) xs (Bitlist.exact (Bitlist.width !!dx) Z.zero Ex.empty)
          in
          update ~ex dx dx'
        ) xs

  let bvand x y z = hcons @@ Band (x, y, z)
  let bvor x y z = hcons @@ Bor (x, y, z)
  let bvxor x y z =
    let xs = SX.singleton x in
    let xs = if SX.mem y xs then SX.remove y xs else SX.add y xs in
    let xs = if SX.mem z xs then SX.remove z xs else SX.add z xs in
    hcons @@ Bxor xs
end

module Constraints = Rel_utils.Constraints_make(Constraint)

let extract_constraints bcs uf r t =
  match E.term_view t with
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

  let propagate c d =
    match c with
    | Constraint { value; explanation = ex } ->
      Constraint.propagate ~ex value d
    | Structural r ->
      Domains.Ephemeral.structural_propagation d r
end

module QC = Uqueue.Make(Any_constraint)

(* Propagate:

   - The constraints that were never propagated since they were added
   - The constraints involving variables whose domain changed since the last
      propagation

   Iterate until fixpoint is reached. *)
let propagate eqs bcs dom =
  (* Optimization to avoid unnecessary allocations *)
  if Constraints.has_pending bcs || Domains.has_changed dom then
    let queue = QC.create 17 in
    Constraints.iter_pending (fun c -> QC.push queue (Constraint c)) bcs;
    let bcs = Constraints.clear_pending bcs in
    let changed = HX.create 17 in
    let touch r =
      HX.replace changed r ();
      QC.push queue (Structural r);
      Constraints.iter_parents (fun c -> QC.push queue (Constraint c)) r bcs
    in
    let dom = Domains.edit dom in
    (
      try
        while true do
          Domains.Ephemeral.iter_changed touch dom;
          Domains.Ephemeral.clear_changed dom;
          Any_constraint.propagate (QC.pop queue) dom
        done
      with QC.Empty -> ()
    );
    HX.fold (fun r () acc ->
        let d = Domains.Ephemeral.(!!(handle dom r)) in
        add_eqs acc (Shostak.Bitv.embed r) d
      ) changed eqs, bcs, Domains.snapshot dom
  else
    eqs, bcs, dom

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
      let ((constraints, domain), eqs, size_splits) =
        List.fold_left (fun ((bcs, dom), eqs, ss) (a, _root, ex, orig) ->
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
              let bcs = Constraints.subst ~ex rr nrr bcs in
              ((bcs, dom), eqs, ss)
            | L.Distinct (false, [rr; nrr]), _ when is_1bit rr ->
              (* We don't (yet) support [distinct] in general, but we must
                 support it for case splits to avoid looping.

                 We are a bit more general and support it for 1-bit vectors, for
                 which `distinct` can be expressed using `bvnot`. *)
              let not_nrr =
                Shostak.Bitv.is_mine (Bitv.lognot (Shostak.Bitv.embed nrr))
              in
              ((bcs, dom), (Uf.LX.mkv_eq rr not_nrr, ex) :: eqs, ss)
            | _ -> ((bcs, dom), eqs, ss)
          )
          ((env.constraints, env.domain), [], env.size_splits)
          la
      in
      let eqs, constraints, domain = propagate eqs constraints domain in
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
          let bcs = extract_constraints env.constraints uf r t in
          let eqs, bcs, dom = propagate eqs bcs dom in
          { env with constraints = bcs ; domain = dom }, eqs
        with Domains.Inconsistent ex ->
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
