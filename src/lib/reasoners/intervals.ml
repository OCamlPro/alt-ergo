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
(*     The Alt-Ergo theorem prover                                        *)
(*                                                                        *)
(*     Sylvain Conchon, Evelyne Contejean, Francois Bobot                 *)
(*     Mohamed Iguernelala, Stephane Lescuyer, Alain Mebsout              *)
(*                                                                        *)
(*     CNRS - INRIA - Universite Paris Sud                                *)
(*                                                                        *)
(*     ---------------------------------------------------------------    *)
(*                                                                        *)
(*     More details can be found in the directory licenses/               *)
(*                                                                        *)
(**************************************************************************)

open Intervals_intf

let src = Logs.Src.create ~doc:"Intervals" __MODULE__
module Log = (val Logs.src_log src : Logs.LOG)

let map_bound f = function
  | Unbounded -> Unbounded
  | Open x -> Open (f x)
  | Closed x -> Closed (f x)

module Ring(C : Core)(RT : RingType) = struct
  include C.Union(RT)

  type monotony = Inc | Dec

  (* Helper to keep the code of [mul] and [ediv] readable. *)
  let map2_mon_to_set f p1 u1 p2 u2 =
    let f_lb, f_ub =
      match p1 with
      | Inc -> (fun i1 -> f i1.lb), (fun i1 -> f i1.ub)
      | Dec -> (fun i1 -> f i1.ub), (fun i1 -> f i1.lb)
    in
    map_mon_to_set (match p2 with
        | Inc -> fun i1 -> approx_map_inc_to_set (f_lb i1) (f_ub i1) u2
        | Dec -> fun i1 -> approx_map_dec_to_set (f_lb i1) (f_ub i1) u2
      ) u1

  let trace1 fname u u' =
    Log.debug (fun m ->
        m "@[%s(%a) = %a@]"
          fname (Fmt.box pp) u (Fmt.box pp) u'
      );
    u'

  let trace2 fname u1 u2 u =
    Log.debug (fun m ->
        m "@[%s(%a, %a) = %a@]"
          fname (Fmt.box pp) u1 (Fmt.box pp) u2 (Fmt.box pp) u
      );
    u

  let neg u = trace1 "neg" u @@ map_strict_dec RT.neg u

  let add u1 u2 =
    trace2 "add" u1 u2 @@ of_set_nonempty @@
    map2_mon_to_set RT.add Inc u1 Inc u2

  let sub u1 u2 = add u1 (neg u2)

  let scale alpha u =
    let alpha = RT.finite alpha in
    let c = RT.compare alpha RT.zero in
    if c < 0 then
      map_strict_dec (RT.mul alpha) u
    else if c > 0 then
      map_strict_inc (RT.mul alpha) u
    else
      invalid_arg "scale: cannot scale by zero"

  let mul u1 u2 =
    trace2 "mul" u1 u2 @@ of_set_nonempty @@
    trisection_map_to_set RT.zero u1
      (fun lt1 ->
         trisection_map_to_set RT.zero u2
           (map2_mon_to_set RT.mul Dec lt1 Dec)
           (fun () -> interval_set { lb = RT.zero ; ub = RT.zero })
           (map2_mon_to_set RT.mul Inc lt1 Dec))
      (fun _ -> interval_set { lb = RT.zero ; ub = RT.zero })
      (fun gt1 ->
         trisection_map_to_set RT.zero u2
           (map2_mon_to_set RT.mul Dec gt1 Inc)
           (fun () -> interval_set { lb = RT.zero ; ub = RT.zero })
           (map2_mon_to_set RT.mul Inc gt1 Inc))

  let pow n u =
    if n <= 0 then Fmt.invalid_arg "pow: nonpositive exponent %d" n;
    if n mod 2 = 0 then
      of_set_nonempty @@
      trisection_map_to_set RT.zero u
        (map_dec_to_set (RT.pow n))
        (fun () -> interval_set { lb = RT.zero ; ub = RT.zero })
        (map_inc_to_set (RT.pow n))
    else
      map_strict_inc (RT.pow n) u
end

module Field(C : Core)(FT : FieldType) = struct
  include Ring(C)(FT)

  let inv ?(inv0 = Interval.full) u =
    (* NB: trisection is required even though we are decreasing on both side,
       because we are not decreasing on ]-oo, +oo[. *)
    trace1 "inv" u @@ of_set_nonempty @@
    trisection_map_to_set FT.zero u
      (map_dec_to_set FT.inv)
      (fun () -> interval_set inv0)
      (map_dec_to_set FT.inv)

  let div ?inv0 x y =
    mul x (inv ?inv0 y)
end

module AlgebraicField(C : Core)(AT : AlgebraicType) = struct
  include Field(C)(AT)

  let root n u =
    if n <= 0 then Fmt.invalid_arg "root: nonpositive radical %d" n;
    of_set_checked @@
    if n mod 2 = 0 then
      trisection_map_to_set AT.zero u
        (fun _ -> empty_set)
        (fun () -> interval_set { lb = AT.zero ; ub = AT.zero })
        (fun gt ->
           let pos =
             approx_map_inc_to_set (AT.root_default n) (AT.root_excess n) gt
           in
           let neg_int i = { lb = AT.neg i.ub ; ub = AT.neg i.lb } in
           union_set (map_set neg_int pos) pos)
    else
      approx_map_inc_to_set (AT.root_default n) (AT.root_excess n) u
end

module EuclideanRing(C : Core)(ET : EuclideanType) = struct
  include Ring(C)(ET)

  let ediv ?(div0 = Interval.full) u1 u2 =
    trace2 "ediv" u1 u2 @@ of_set_nonempty @@
    trisection_map_to_set ET.zero u2
      (fun lt2 ->
         trisection_map_to_set ET.zero u1
           (fun lt1 -> map2_mon_to_set ET.ediv Dec lt1 Inc lt2)
           (fun () -> interval_set { lb = ET.zero ; ub = ET.zero })
           (fun gt1 -> map2_mon_to_set ET.ediv Dec gt1 Dec lt2))
      (fun () -> interval_set div0)
      (fun gt2 ->
         trisection_map_to_set ET.zero u1
           (fun lt1 -> map2_mon_to_set ET.ediv Inc lt1 Inc gt2)
           (fun () -> interval_set { lb = ET.zero ; ub = ET.zero })
           (fun gt1 -> map2_mon_to_set ET.ediv Inc gt1 Dec gt2))
end

(* EuclideanType interface for integers: all intervals are closed, but we still
   need to handle infinities. *)
module ZEuclideanType = struct
  type finite = Z.t

  let pp_finite = Z.pp_print

  type t = Neg_infinite | Finite of finite | Pos_infinite

  let pp ppf = function
    | Neg_infinite -> Format.fprintf ppf "-oo"
    | Finite n -> pp_finite ppf n
    | Pos_infinite -> Format.fprintf ppf "+oo"

  let equal x y =
    match x, y with
    | Neg_infinite, Neg_infinite -> true
    | Neg_infinite, _ | _, Neg_infinite -> false

    | Pos_infinite, Pos_infinite -> true
    | Pos_infinite, _ | _, Pos_infinite -> false

    | Finite x, Finite y -> Z.equal x y

  let compare x y =
    match x, y with
    | Neg_infinite, Neg_infinite -> 0
    | Neg_infinite, _ -> -1
    | _, Neg_infinite -> 1

    | Finite x, Finite y -> Z.compare x y

    | Pos_infinite, Pos_infinite -> 0
    | Pos_infinite, _ -> 1
    | _, Pos_infinite -> -1

  let minfty = Neg_infinite

  let finite n = Finite n

  let pinfty = Pos_infinite

  let value_opt = function Finite n -> Some n | _ -> None

  let succ = function
    | Finite x -> Finite (Z.succ x)
    | inf -> inf

  let pred = function
    | Finite x -> Finite (Z.pred x)
    | inf -> inf

  let view = function
    | Neg_infinite | Pos_infinite -> Unbounded
    | Finite x -> Closed x

  let zero = Finite Z.zero

  let sign = function
    | Neg_infinite -> -1
    | Finite n -> Z.sign n
    | Pos_infinite -> 1

  let neg = function
    | Neg_infinite -> Pos_infinite
    | Finite n -> Finite (Z.neg n)
    | Pos_infinite -> Neg_infinite

  let add x y =
    match x, y with
    | Pos_infinite, Neg_infinite | Neg_infinite, Pos_infinite ->
      Fmt.invalid_arg "add: %a + %a is undefined" pp x pp y

    | Pos_infinite, _ | _, Pos_infinite -> Pos_infinite
    | Neg_infinite, _ | _, Neg_infinite -> Neg_infinite

    | Finite x, Finite y -> Finite (Z.add x y)

  let mul x y =
    match x, y with
    | (Pos_infinite | Neg_infinite), (Pos_infinite | Neg_infinite) ->
      if sign x = sign y then Pos_infinite else Neg_infinite

    | Finite x, Finite y -> Finite (Z.mul x y)

    | Finite fin, (Pos_infinite | Neg_infinite as inf)
    | (Pos_infinite | Neg_infinite as inf), Finite fin ->
      let s = Z.sign fin in
      if s > 0 then inf
      else if s < 0 then neg inf
      else Finite Z.zero

  let pow n x =
    if n <= 0 then Fmt.invalid_arg "pow: nonpositive exponent %d" n;
    match x with
    | Pos_infinite -> Pos_infinite
    | Neg_infinite ->
      if n mod 2 = 0 then Pos_infinite else Neg_infinite
    | Finite x -> Finite (Z.pow x n)

  let ediv x y =
    match x, y with
    | Pos_infinite, Pos_infinite
    | Neg_infinite, Neg_infinite ->
      Pos_infinite

    | Neg_infinite, Pos_infinite
    | Pos_infinite, Neg_infinite ->
      Neg_infinite

    | Finite x, Finite y -> Finite (Z.ediv x y)

    | Pos_infinite, Finite x ->
      if Z.sign x > 0 then Pos_infinite else Neg_infinite

    | Neg_infinite, Finite x ->
      if Z.sign x < 0 then Pos_infinite else Neg_infinite

    | Finite x, Pos_infinite ->
      if Z.sign x < 0 then Finite Z.minus_one else Finite Z.zero

    | Finite x, Neg_infinite ->
      if Z.sign x < 0 then Finite Z.one else Finite Z.zero

  let lognot = function
    | Neg_infinite -> Pos_infinite
    | Pos_infinite -> Neg_infinite
    | Finite n -> Finite (Z.lognot n)

  (* Values larger than [max_int] are treated as +oo *)
  let shift_left ?(max_int = max_int) x y =
    let[@inline always] must_be_nonnegative () =
      Fmt.invalid_arg "shl: must shift by nonnegative amount"
    in
    match y with
    | Neg_infinite -> must_be_nonnegative ()
    | Finite y when Z.sign y < 0 -> must_be_nonnegative ()
    | Pos_infinite -> Pos_infinite
    | Finite y ->
      match Z.to_int y with
      | exception Z.Overflow -> Pos_infinite
      | y ->
        if y <= max_int then
          match x with
          | Neg_infinite -> Neg_infinite
          | Pos_infinite -> Pos_infinite
          | Finite x -> Finite (Z.shift_left x y)
        else Pos_infinite

  let shift_right x y =
    match y with
    | Neg_infinite ->
      invalid_arg "shift_right: must shift by nonnegative amount"
    | Finite y when Z.sign y < 0 ->
      invalid_arg "shift_right: must shift by nonnegative amount"
    | Pos_infinite -> (
        match x with
        | Pos_infinite -> invalid_arg "shift_right: undefined limit"
        | _ -> zero
      )
    | Finite y ->
      match x with
      | Neg_infinite -> Neg_infinite
      | Pos_infinite -> Pos_infinite
      | Finite x ->
        match Z.to_int y with
        | exception Z.Overflow ->
          (* y > max_int -> x >> y = 0 since numbits x <= max_int *)
          zero
        | y -> Finite (Z.shift_right x y)
end

(* AlgebraicType interface for reals

   In order to deal with open intervals, we allow bounds of the form [x + eps]
   and [x - eps] where [eps] is an infinitesimal. Effectively, [x + eps] is a
   strict lower bound, and [x - eps] is a strict upper bound. *)
module QAlgebraicType = struct
  type finite = Q.t

  let pp_finite = Q.pp_print

  type kind = Lt | Eq | Gt
  (* We store bounds as pairs [(kind, v)] where [(Lt, v)] denotes [v - eps] or
     the upper bound [x < v]] and [(Gt, v)] denotes [v + eps] or the lower bound
     [x > v]. *)

  let pp_kind pp ppf (k, x) =
    match k with
    | Lt -> Format.fprintf ppf "%a-eps" pp x
    | Eq -> pp ppf x
    | Gt -> Format.fprintf ppf "%a+eps" pp x

  let equal_kind x y =
    match x, y with
    | Lt, Lt -> true
    | Lt, _ | _, Lt -> false

    | Gt, Gt -> true
    | Gt, _ | _, Gt -> false

    | Eq, Eq -> true

  let compare_kind x y =
    match x, y with
    | Lt, Lt -> 0
    | Lt, _ -> -1
    | _, Lt -> 1

    | Eq, Eq -> 0

    | Gt, Gt -> 0
    | Gt, _ -> 1
    | _, Gt -> -1

  type t = Neg_infinite | Finite of kind * finite | Pos_infinite

  let of_bigint = function
    | ZEuclideanType.Neg_infinite -> Neg_infinite
    | Finite n -> Finite (Eq, Q.of_bigint n)
    | Pos_infinite -> Pos_infinite

  let floor = function
    | Neg_infinite -> ZEuclideanType.Neg_infinite
    | Finite (k, x) ->
      (* If [y < x] with [x] an integer, then [floor(y) <= x - 1] *)
      if Z.equal (Q.den x) Z.one then
        match k with
        | Lt -> Finite (Z.pred @@ Q.num x)
        | Eq | Gt -> Finite (Q.num x)
      else
        Finite (Z.fdiv (Q.num x) (Q.den x))
    | Pos_infinite -> Pos_infinite

  let ceiling = function
    | Neg_infinite -> ZEuclideanType.Neg_infinite
    | Finite (k, x) ->
      (* If [x < y] with [x] an integer, then [x + 1 <= ceiling(y)] *)
      if Z.equal (Q.den x) Z.one then
        match k with
        | Lt | Eq -> Finite (Q.num x)
        | Gt -> Finite (Z.succ @@ Q.num x)
      else
        Finite (Z.cdiv (Q.num x) (Q.den x))
    | Pos_infinite -> Pos_infinite

  let pp ppf = function
    | Neg_infinite -> Format.fprintf ppf "-oo"
    | Finite (k, x) -> pp_kind pp_finite ppf (k, x)
    | Pos_infinite -> Format.fprintf ppf "+oo"

  let equal x y =
    match x, y with
    | Neg_infinite, Neg_infinite -> true
    | Neg_infinite, _ | _, Neg_infinite -> false

    | Pos_infinite, Pos_infinite -> true
    | Pos_infinite, _ | _, Pos_infinite -> false

    | Finite (kx, x), Finite (ky, y) ->
      Q.equal x y && equal_kind kx ky

  let compare x y =
    match x, y with
    | Neg_infinite, Neg_infinite -> 0
    | Neg_infinite, _ -> -1
    | _, Neg_infinite -> 1

    | Finite (kx, x), Finite (ky, y) ->
      let c = Q.compare x y in
      if c <> 0 then c else
        compare_kind kx ky

    | Pos_infinite, Pos_infinite -> 0
    | Pos_infinite, _ -> 1
    | _, Pos_infinite -> -1

  let minfty = Neg_infinite

  let finite x = Finite (Eq, x)

  let pinfty = Pos_infinite

  let value_opt = function Finite (Eq, x) -> Some x | _ -> None

  let succ = function
    | Finite (Lt, x) -> Finite (Eq, x)
    | Finite (Eq, x) -> Finite (Gt, x)
    | Finite (Gt, _) as x ->
      Fmt.invalid_arg "succ: %a" pp x
    | inf -> inf

  let pred = function
    | Finite (Lt, _) as x ->
      Fmt.invalid_arg "pred: %a" pp x
    | Finite (Eq, x) -> Finite (Lt, x)
    | Finite (Gt, x) -> Finite (Eq, x)
    | inf -> inf

  let view = function
    | Neg_infinite | Pos_infinite -> Unbounded
    | Finite (Eq, x) -> Closed x
    | Finite (_, x) -> Open x

  let zero = Finite (Eq, Q.zero)

  let sign_kind = function
    | Lt -> -1
    | Eq -> 0
    | Gt -> 1

  let kind_of_sign s =
    if s < 0 then Lt else if s > 0 then Gt else Eq

  let neg_kind k = kind_of_sign (-sign_kind k)

  let neg = function
    | Pos_infinite -> Neg_infinite
    | Neg_infinite -> Pos_infinite
    | Finite (k, x) -> Finite (neg_kind k, Q.neg x)

  let add x y =
    match x, y with
    | Pos_infinite, Pos_infinite
    | Pos_infinite, Finite _
    | Finite _, Pos_infinite ->
      Pos_infinite

    | Neg_infinite, Neg_infinite
    | Neg_infinite, Finite _
    | Finite _, Neg_infinite ->
      Neg_infinite

    | Finite (kx, qx), Finite (ky, qy) ->
      (* Can never add lower bound to upper bound *)
      let skx = sign_kind kx and sky = sign_kind ky in
      if (skx * sky < 0) then
        Fmt.invalid_arg "add: %a + %a" pp x pp y;
      Finite (kind_of_sign (sign_kind kx + sign_kind ky), Q.add qx qy)

    | Pos_infinite, Neg_infinite
    | Neg_infinite, Pos_infinite ->
      Fmt.invalid_arg "add: %a + %a is undefined" pp x pp y

  let sign = function
    | Neg_infinite -> -1
    | Pos_infinite -> 1
    | Finite (k, x) ->
      let s = Q.sign x in
      if s <> 0 then s else
        sign_kind k

  let mul x y =
    match x, y with
    | Pos_infinite, Pos_infinite
    | Neg_infinite, Neg_infinite ->
      Pos_infinite

    | Pos_infinite, Neg_infinite
    | Neg_infinite, Pos_infinite ->
      Neg_infinite

    | (Pos_infinite | Neg_infinite as i), (Finite _ as f)
    | (Finite _ as f), (Pos_infinite | Neg_infinite as i) ->
      let s = sign f in
      if s > 0 then i
      else if s < 0 then neg i
      else Finite (Eq, Q.zero)

    | Finite (kx, qx), Finite (ky, qy) ->
      let sx = sign x and sy = sign y in
      if sx = 0 || sy = 0 then
        Finite (Eq, Q.zero)
      else
        let skx = sign_kind kx and sky = sign_kind ky in
        (* Check that [x] and [y] do not have opposite epsilon if they
           have the same sign, or identical epsilon if they have opposite
           signs: this matches the monotonicity of multiplication. *)
        assert (skx = 0 || sky = 0 || sx * sy = skx * sky);
        let k = kind_of_sign (skx * sy + sky * sx) in
        Finite (k, Q.mul qx qy)

  let pow n x =
    if n <= 0 then Fmt.invalid_arg "pow: nonpositive exponent %d" n;
    match x with
    | Pos_infinite -> Pos_infinite
    | Neg_infinite ->
      if n mod 2 = 0 then Pos_infinite else Neg_infinite
    | Finite (k, qx) ->
      let qpow = Q.make (Z.pow (Q.num qx) n) (Z.pow (Q.den qx) n) in
      if n mod 2 = 0 && sign x < 0 then
        Finite (neg_kind k, qpow)
      else
        Finite (k, qpow)

  let inv = function
    | Neg_infinite -> Finite (Lt, Q.zero)
    | Pos_infinite -> Finite (Gt, Q.zero)
    | Finite (k, x) ->
      if Q.(x = zero) then
        match k with
        | Lt -> Neg_infinite
        | Eq -> Fmt.invalid_arg "inv: 1/0 is undefined"
        | Gt -> Pos_infinite
      else
        Finite (neg_kind k, Q.inv x)

  let root_default_num n v =
    if n = 2 then Numbers.Q.sqrt_default v else Numbers.Q.root_default v n

  let root_excess_num n v =
    if n = 2 then Numbers.Q.sqrt_excess v else Numbers.Q.root_excess v n

  let root_default n = function
    | Neg_infinite -> Neg_infinite
    | Pos_infinite -> Pos_infinite
    | Finite (_, x) ->
      match
        if Q.sign x >= 0 then root_default_num n x
        else Option.map Q.neg (root_excess_num n (Q.neg x))
      with
      | None -> Neg_infinite
      | Some x -> Finite (Eq, x)

  let root_excess n = function
    | Neg_infinite -> Neg_infinite
    | Pos_infinite -> Pos_infinite
    | Finite (_, x) ->
      match
        if Q.sign x >= 0 then root_excess_num n x
        else Option.map Q.neg (root_default_num n (Q.neg x))
      with
      | None -> Pos_infinite
      | Some x -> Finite (Eq, x)

  let ( + ) = add

  let ( * ) = mul

  let (~$$) = of_bigint
end

module Core = Intervals_core.Make(struct
    include Explanation

    let pp = print
  end)

type 'a union = 'a Core.union

module Real = AlgebraicField(Core)(QAlgebraicType)

module Int = struct
  include EuclideanRing(Core)(ZEuclideanType)

  let extract u ~ofs ~len =
    if ofs < 0 || len <= 0 then invalid_arg "extract";
    trace1 (Fmt.str "extract ~ofs:%d ~len:%d" ofs len) u @@
    let max_val = Z.extract Z.minus_one 0 len in
    let full = Interval.of_bounds (Closed Z.zero) (Closed max_val) in
    of_set_nonempty @@
    map_to_set (fun i ->
        match i.lb, i.ub with
        | ZEuclideanType.Neg_infinite, _ | _, Pos_infinite ->
          interval_set full
        | _, Neg_infinite | Pos_infinite, _ ->
          assert false
        | Finite lb, Finite ub ->
          let lb = Z.shift_right lb ofs in
          let ub = Z.shift_right ub ofs in
          if Z.(numbits (ub - lb)) <= len then
            (* The image spans an interval of length at most [len] *)
            let lb_mod = Z.extract lb 0 len in
            let ub_mod = Z.extract ub 0 len in
            if Z.(compare lb_mod ub_mod) <= 0 then
              interval_set @@ Interval.of_bounds (Closed lb_mod) (Closed ub_mod)
            else
              union_set
                (interval_set @@ Interval.of_bounds
                   (Closed Z.zero) (Closed ub_mod))
                (interval_set @@ Interval.of_bounds
                   (Closed lb_mod) (Closed max_val))
          else
            (* The image is too large; all values are possible. *)
            interval_set full
      ) u

  let lognot u =
    trace1 "lognot" u @@ map_strict_dec ZEuclideanType.lognot u

  let bvudiv ~size:sz u1 u2 =
    (* [bvudiv] is euclidean division where division by zero is -1 (as an
       integer of width [sz], so 2^sz - 1) *)
    let mone = Z.extract Z.minus_one 0 sz in
    ediv ~div0:(Interval.of_bounds (Closed mone) (Closed mone)) u1 u2

  let bvurem u1 u2 =
    (* In the following, [x] is the implicit variable associated with [u1] and
       [y] the implicit variable associated with [u2]. *)
    of_set_nonempty @@
    map_to_set (fun i2 ->
        if ZEuclideanType.equal i2.ub ZEuclideanType.zero then
          (* [y] is always zero -> identity *)
          map_to_set interval_set u1
        else if ZEuclideanType.compare i2.ub ZEuclideanType.zero < 0 then
          (* Safety check -- bvurem only makes sense if [u2] is nonnegative. *)
          invalid_arg "bvurem"
        else
          map_to_set (fun i1 ->
              if ZEuclideanType.compare i1.ub i2.lb < 0 then
                (* x < y : bvurem is the identity *)
                interval_set i1
              else if (
                ZEuclideanType.equal i2.lb ZEuclideanType.zero
              ) then
                (* The range [0, i1.ub] is always valid; it is also the best we
                   can do if [y] can be [0]. *)
                interval_set { i1 with lb = ZEuclideanType.zero }
              else
                (* y is non-zero; we have both [x % y < y] and [x % y <= x] so
                   take the min of these upper bounds. *)
                let ub =
                  if ZEuclideanType.compare i1.ub i2.ub < 0 then i1.ub
                  else ZEuclideanType.pred i2.ub
                in
                interval_set { lb = ZEuclideanType.zero ; ub }
            ) u1
      ) u2

  let bvshl ~size u1 u2 =
    assert (size > 0);
    (* Values higher than [max_int] ultimately map to [0] *)
    let max_int = size - 1 in
    let zero_i = { lb = ZEuclideanType.zero ; ub = ZEuclideanType.zero } in
    extract ~ofs:0 ~len:size @@
    of_set_nonempty @@
    map_to_set (fun i2 ->
        assert (ZEuclideanType.sign i2.lb >= 0);
        if ZEuclideanType.(compare i2.lb (finite @@ Z.of_int max_int)) > 0 then
          (* if i2.lb > max_int, the result is always zero
             must not call ZEuclideanType.shift_left or we will likely OOM *)
          interval_set zero_i
        else
          (* equivalent to multiplication by a positive constant *)
          approx_map_inc_to_set
            (fun lb -> ZEuclideanType.shift_left lb i2.lb)
            (fun ub -> ZEuclideanType.shift_left ~max_int ub i2.ub)
            u1
      ) u2

  let lshr u1 u2 =
    of_set_nonempty @@
    map2_mon_to_set ZEuclideanType.shift_right Inc u1 Dec u2
end

module Legacy = struct
  type t = Real of Real.t | Int of Int.t

  let pretty_print ppf = function
    | Real u -> Real.pp ppf u
    | Int u -> Int.pp ppf u

  let print = pretty_print

  let of_real u = Real u

  let of_int u = Int u

  exception NotConsistent of Explanation.t

  let check = function
    | NonEmpty u -> u
    | Empty ex -> raise @@ NotConsistent ex

  exception No_finite_bound

  let undefined ty =
    match ty with
    | Ty.Tint -> of_int @@ Int.of_interval @@ Int.Interval.full
    | Treal -> of_real @@ Real.of_interval @@ Real.Interval.full
    | _ -> invalid_arg "undefined"

  let point v ty ex =
    match ty with
    | Ty.Treal ->
      of_real @@ Real.of_interval ~ex @@ Real.Interval.singleton v
    | Tint when Z.equal (Q.den v) Z.one ->
      of_int @@ Int.of_interval ~ex @@ Int.Interval.singleton @@ Q.num v
    | _ -> Fmt.invalid_arg "point: %a (as %a)" Q.pp_print v Ty.print ty

  let doesnt_contain_0 u =
    Option.map (fun ex -> (ex, [])) @@
    match u with
    | Real u -> Real.(
        match intersect u (of_interval @@ Interval.singleton Q.zero) with
        | NonEmpty _ -> None
        | Empty ex -> Some ex
      )
    | Int u -> Int.(
        match intersect u (of_interval @@ Interval.singleton Z.zero) with
        | NonEmpty _ -> None
        | Empty ex -> Some ex
      )

  let is_strict_smaller u1 u2 =
    match u1, u2 with
    | Real u1, Real u2 -> Real.subset ~strict:true u1 u2
    | Int u1, Int u2 -> Int.subset ~strict:true u1 u2
    | Int _, Real _ | Real _, Int _ -> invalid_arg "is_strict_smaller"

  let new_borne_sup ex b ~is_le u =
    match u with
    | Real u ->
      let ub = if is_le then Closed b else Open b in
      of_real @@ check @@ Real.intersect u @@ Real.of_bounds ~ex Unbounded ub
    | Int u ->
      let b = Z.fdiv (Q.num b) (Q.den b) in
      let ub = if is_le then Closed b else Open b in
      of_int @@ check @@ Int.intersect u @@ Int.of_bounds ~ex Unbounded ub

  let new_borne_inf ex b ~is_le u =
    match u with
    | Real u ->
      let lb = if is_le then Closed b else Open b in
      of_real @@ check @@ Real.intersect u @@ Real.of_bounds ~ex lb Unbounded
    | Int u ->
      let b = Z.cdiv (Q.num b) (Q.den b) in
      let lb = if is_le then Closed b else Open b in
      of_int @@ check @@ Int.intersect u @@ Int.of_bounds ~ex lb Unbounded

  let only_borne_sup= function
    | Real u ->
      let ub, ex = Real.upper_bound u in
      of_real @@ Real.of_bounds ~ex Unbounded ub
    | Int u ->
      let ub, ex = Int.upper_bound u in
      of_int @@ Int.of_bounds ~ex Unbounded ub

  let only_borne_inf = function
    | Real u ->
      let lb, ex = Real.lower_bound u in
      of_real @@ Real.of_bounds ~ex lb Unbounded
    | Int u ->
      let lb, ex = Int.lower_bound u in
      of_int @@ Int.of_bounds ~ex lb Unbounded

  let is_point = function
    | Real u -> Real.value_opt u
    | Int u -> (
        match Int.value_opt u with
        | Some (v, ex) -> Some (Q.of_bigint v, ex)
        | _ -> None
      )

  let intersect u1 u2 =
    match u1, u2 with
    | Real u1, Real u2 -> of_real @@ check @@ Real.intersect u1 u2
    | Int u1, Int u2 -> of_int @@ check @@ Int.intersect u1 u2
    | Int _, Real _ | Real _, Int _ -> invalid_arg "intersect"

  let exclude ?ex v u =
    match u with
    | Real u -> (
        let v = Real.Interval.singleton v in
        match Real.intersect u @@ check @@ Real.of_complement ?ex v with
        | NonEmpty u -> of_real u
        | Empty ex -> raise @@ NotConsistent ex
      )
    | Int u -> (
        if Z.equal (Q.den v) Z.one then
          let v = Int.Interval.singleton @@ Q.num v in
          match Int.intersect u @@ check @@ Int.of_complement ?ex v with
          | NonEmpty u -> of_int u
          | Empty ex -> raise @@ NotConsistent ex
        else
          Int u
      )

  let map2 fname freal fint u1 u2 =
    match u1, u2 with
    | Real u1, Real u2 -> of_real (freal u1 u2)
    | Int u1, Int u2 -> of_int (fint u1 u2)
    | _ ->
      Fmt.invalid_arg "%s: cannot %s int and real"
        fname fname

  let mult = map2 "mult" Real.mul Int.mul

  let power n = function
    | Real u -> of_real @@ Real.pow n u
    | Int u -> of_int @@ Int.pow n u

  let root n = function
    | Real u -> of_real @@ check @@ Real.root n u
    | Int _ -> invalid_arg "root: cannot take integral root"

  let add = map2 "add" Real.add Int.add

  let neg = function
    | Real u -> of_real @@ Real.neg u
    | Int u -> of_int @@ Int.neg u

  let affine_scale ~const ~coef u =
    let coef, u =
      let c = Q.sign coef in
      if c < 0 then Q.neg coef, neg u
      else if c > 0 then coef, u
      else Fmt.invalid_arg "affine: scale cannot be zero"
    in
    let open QAlgebraicType in
    let scale = finite coef in
    let offset = finite const in
    match u with
    | Real u ->
      of_real @@ Real.map_strict_inc (fun b -> b * scale + offset) u
    | Int u ->
      of_int @@ check @@
      Int.partial_map_inc
        (fun lb -> ceiling @@ ~$$lb * scale + offset)
        (fun ub -> floor @@ ~$$ub * scale + offset)
        u

  let scale scale u = affine_scale ~const:Q.zero ~coef:scale u

  let finite_size u =
    match u with
    | Int u -> (
        try
          Some (
            Q.of_bigint @@
            Int.fold (fun acc i ->
                match Int.Interval.view i with
                | { lb = Closed lb ; ub = Closed ub } -> Z.(acc + ub - lb + one)
                | _ -> raise Exit
              ) Z.zero u
          )
        with Exit -> None
      )
    | _ -> None

  let integer_hull = function
    | Real _ -> invalid_arg "integer_hull"
    | Int u ->
      let lb, ex_lb = Int.lower_bound u in
      let ub, ex_ub = Int.upper_bound u in
      let lb =
        match lb with
        | Closed v -> Some (v, ex_lb)
        | _ -> None
      in
      let ub =
        match ub with
        | Closed v -> Some (v, ex_ub)
        | _ -> None
      in
      (lb, ub)

  let lower_bound = function
    | Real u -> Real.lower_bound u
    | Int u ->
      let lb, ex_lb = Int.lower_bound u in
      map_bound Q.of_bigint lb, ex_lb

  let borne_inf u =
    let lb, ex = lower_bound u in
    match lb with
    | Open b -> b, ex, false
    | Closed b -> b, ex, true
    | Unbounded -> raise No_finite_bound

  let upper_bound = function
    | Real u -> Real.upper_bound u
    | Int u ->
      let ub, ex_ub = Int.upper_bound u in
      map_bound Q.of_bigint ub, ex_ub

  let borne_sup u =
    let ub, ex = upper_bound u in
    match ub with
    | Open b -> b, ex, false
    | Closed b -> b, ex, true
    | Unbounded -> raise No_finite_bound

  let div = map2 "div" Real.div Int.ediv

  let coerce ty u =
    match ty, u with
    | Ty.Treal, Real _ -> u
    | Treal, Int u ->
      of_real @@ Real.map_strict_inc QAlgebraicType.of_bigint u
    | Tint, Int _ -> u
    | Tint, Real u ->
      of_int @@ check @@
      Int.partial_map_inc QAlgebraicType.ceiling QAlgebraicType.floor u
    | _ -> Fmt.invalid_arg "coerce"

  let contains u v =
    match u with
    | Real u -> Real.(
        match intersect u (of_interval @@ Interval.singleton v) with
        | NonEmpty _ -> true
        | Empty _ -> false
      )
    | Int u -> Int.(
        if Z.equal (Q.den v) Z.one then
          let v = Q.num v in
          match intersect u (of_interval @@ Interval.singleton v) with
          | NonEmpty _ -> true
          | Empty _ -> false
        else
          false
      )

  let add_explanation u ex =
    match u with
    | Real u -> Real (Real.add_explanation ~ex u)
    | Int u -> Int (Int.add_explanation ~ex u)

  let equal u1 u2 =
    match u1, u2 with
    | Real u1, Real u2 -> Real.equal u1 u2
    | Int u1, Int u2 -> Int.equal u1 u2
    | _ -> invalid_arg "equal"

  let pick ~is_max u =
    match u with
    | Real u ->
      let pick_interval lb ub =
        match lb, ub with
        | Unbounded, Unbounded -> Q.zero

        | _, Closed ub when is_max -> ub

        | Unbounded, Open ub when is_max -> Q.(ub - ~$1)
        | (Open lb | Closed lb), Open ub when is_max ->
          Q.(ub - min ~$1 ((ub - lb) / ~$2))

        | (Open lb | Closed lb), Unbounded when is_max -> Q.(lb + ~$1)

        | Closed lb, _ -> lb
        | Open lb, Unbounded -> Q.(lb + ~$1)
        | Open lb, (Open ub | Closed ub) ->
          Q.(lb + min ~$1 ((ub - lb) / ~$2))
        | Unbounded, (Open ub | Closed ub) -> Q.(ub - ~$1)
      in
      let lb, _ = Real.lower_bound u in
      let ub, _ = Real.upper_bound u in
      Real.fold (fun acc i ->
          let i = Real.Interval.view i in
          (if is_max then max else min) acc (pick_interval i.lb i.ub)
        ) (pick_interval lb ub) u
    | Int u ->
      let pick_interval lb ub =
        match lb, ub with
        | Unbounded, Unbounded -> Z.zero

        | _, Closed ub when is_max -> ub
        | Closed lb, Unbounded when is_max -> Z.succ lb

        | Closed lb, _ -> lb
        | Unbounded, Closed ub -> Z.pred ub

        | Open _, _ | _, Open _ -> assert false
      in
      let lb, _ = Int.lower_bound u in
      let ub, _ = Int.upper_bound u in
      let n =
        Int.fold (fun acc i ->
            let i = Int.Interval.view i in
            (if is_max then max else min) acc (pick_interval i.lb i.ub)
          ) (pick_interval lb ub) u
      in
      Q.of_bigint n

  let fold f acc u =
    match u with
    | Real u ->
      Real.fold (fun acc i -> f acc (Real.Interval.view i)) acc u
    | Int u ->
      Int.fold (fun acc i ->
          f acc
            (Real.Interval.view
               { lb = QAlgebraicType.of_bigint i.lb
               ; ub = QAlgebraicType.of_bigint i.ub })
        ) acc u

  type interval_matching =
    ((Q.t * bool) option * (Q.t * bool) option * Ty.t) Var.Map.t

  module MV = Var.Map
  module Sy = Symbols

  let consistent_bnds low up =
    match low, up with
    | Some (q_low, str_low), Some (q_up, str_up) ->
      let c = Q.compare q_up q_low in
      c > 0 || (c = 0 && not str_low && not str_up)
    | _ -> true

  let new_up_bound idoms s ty q is_strict =
    let old_low, old_up, ty =
      try MV.find s idoms
      with Not_found -> None,None,ty
    in
    let new_up =
      match old_up with
      | None -> Some (q, is_strict)
      | Some (r, str)  ->
        let c = Q.compare r q in
        if c < 0 then old_up
        else if c > 0 then Some (q, is_strict)
        else
        if is_strict == str || is_strict then old_up
        else Some (q, is_strict)
    in
    if new_up == old_up then idoms
    else
    if consistent_bnds old_low new_up then MV.add s (old_low, new_up, ty) idoms
    else raise Exit

  let new_low_bound idoms s ty q is_strict =
    let old_low, old_up, ty =
      try MV.find s idoms
      with Not_found -> None,None,ty
    in
    let new_low =
      match old_low with
      | None -> Some (q, is_strict)
      | Some (r, str)  ->
        let c = Q.compare r q in
        if c > 0 then old_low
        else if c < 0 then Some (q, is_strict)
        else
        if is_strict == str || is_strict then old_low
        else Some (q, is_strict)
    in
    if new_low == old_low then idoms
    else
    if consistent_bnds new_low old_up then MV.add s (new_low, old_up, ty) idoms
    else raise Exit

  let new_var idoms s ty =
    if MV.mem s idoms then idoms
    else MV.add s (None, None, ty) idoms

  let match_interval_upper {Symbols.sort; is_open; kind; is_lower} u imatch =
    assert (not is_lower);
    match kind, fst (upper_bound u) with
    | Unbounded, _ -> imatch (* ? var *)
    | VarBnd s, Unbounded -> new_var imatch s sort
    | VarBnd s, Open v -> new_low_bound imatch s sort v false
    | VarBnd s, Closed v -> new_low_bound imatch s sort v is_open

    | ValBnd _, Unbounded -> raise Exit
    | ValBnd vl, Open v ->
      if Q.compare v vl > 0 then raise Exit;
      imatch
    | ValBnd vl, Closed v ->
      let c = Q.compare v vl in
      if c > 0 || c = 0 && is_open then raise Exit;
      imatch

  let match_interval_lower {Symbols.sort; is_open; kind; is_lower} u imatch =
    assert is_lower;
    match kind, fst (lower_bound u) with
    | Unbounded, _ -> imatch (* ? var *)

    | VarBnd s, Unbounded -> new_var imatch s sort
    | VarBnd s, Open v -> new_up_bound imatch s sort v false
    | VarBnd s, Closed v -> new_up_bound imatch s sort v is_open

    | ValBnd _, Unbounded -> raise Exit
    | ValBnd vl, Open v ->
      if Q.compare v vl < 0 then raise Exit;
      imatch
    | ValBnd vl, Closed v ->
      let c = Q.compare v vl in
      if c < 0 || c = 0 && is_open then raise Exit;
      imatch

  let match_interval lb ub u acc =
    try Some (match_interval_upper ub u (match_interval_lower lb u acc))
    with Exit -> None
end

module DebugExplanations : Explanations with type t = string list = struct
  (** This module implements the [Explanations] interface by storing
      explanations as (sorted) lists of strings for debugging purposes. *)

  type t = string list

  let pp ppf ex =
    Format.fprintf ppf "@[[%a]@]"
      (Format.pp_print_list
         ~pp_sep:(fun ppf () -> Format.fprintf ppf ",@ ")
         Format.pp_print_string) ex

  let is_empty = function
    | [] -> true
    | _ -> false

  let empty = []

  let union l1 l2 =
    List.rev_append l1 l2 |> List.sort_uniq String.compare

  let compare l1 l2 =
    Compat.List.compare String.compare l1 l2
end
