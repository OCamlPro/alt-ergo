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

(** Literal floating-point values. *)

module Q = Numbers.Q

type t =
  | Plus_infinity
  | Minus_infinity
  | Plus_zero
  | Minus_zero
  | NaN
  | Finite of Q.t

let compare v1 v2 =
  Util.compare_algebraic v1 v2 (function
    | Finite q1, Finite q2 -> Q.compare q1 q2
    | ( _,
        ( Plus_infinity | Minus_infinity | Plus_zero | Minus_zero | NaN
        | Finite _ ) ) ->
      assert false)

let equal v1 v2 =
  match v1, v2 with
  | Plus_infinity, Plus_infinity
  | Minus_infinity, Minus_infinity
  | Plus_zero, Plus_zero
  | Minus_zero, Minus_zero
  | NaN, NaN ->
    true
  | Finite q1, Finite q2 -> Q.equal q1 q2
  | ( (Plus_infinity | Minus_infinity | Plus_zero | Minus_zero | NaN | Finite _),
      _ ) ->
    false

(* This works because we know that [q] is always dyadic since its created from
   an SMT-LIB float literal. *)
let hex_of_q q =
  let sign = if Q.sign q < 0 then "-" else "" in
  let num = Z.abs (Q.num q) in
  let k = Z.numbits (Q.den q) - 1 in
  assert (Z.equal (Q.den q) (Z.shift_left Z.one k));
  Fmt.str "%s0x%sp-%d" sign (Z.format "%x" num) k

let pp ppf = function
  | Plus_infinity -> Fmt.pf ppf "+oo"
  | Minus_infinity -> Fmt.pf ppf "-oo"
  | Plus_zero -> Fmt.pf ppf "+zero"
  | Minus_zero -> Fmt.pf ppf "-zero"
  | NaN -> Fmt.pf ppf "NaN"
  | Finite q -> Fmt.pf ppf "fp[%s]" (hex_of_q q)

(* bias = 2^(eb-1) - 1 *)
let bias ~eb = (1 lsl (eb - 1)) - 1

(* min_exp = bias + sb - 2 *)
let min_exp ~eb ~sb = bias ~eb + sb - 2

(* rational value -> (neg, biased_exp, significand) *)
let q_to_bvs ~eb ~sb q =
  let bias = bias ~eb in
  let min_exp = min_exp ~eb ~sb in
  let neg = Q.sign q < 0 in
  let a = Q.abs q in
  (* q is decoded from a float literal: |q| = n / 2^k. (m, e) with m*2^e = |q|,
     e = max(floor(log2|q|) + 1 - sb, -min_exp), where floor(log2|q|) =
     numbits(n) - 1 - k. *)
  let k = Z.numbits (Q.den a) - 1 in
  let e = max (Z.numbits (Q.num a) - k - sb) (-min_exp) in
  let mq = if e >= 0 then Q.div_2exp a e else Q.mult_2exp a (-e) in
  (* The literal is exact: m is an integer and m < 2^sb. *)
  assert (Z.equal (Q.den mq) Z.one);
  let m = Q.num mq in
  assert (Z.numbits m <= sb);
  (* hidden_bit = 2^(sb-1) *)
  let hidden_bit = Z.shift_left Z.one (sb - 1) in
  let biased_exp, significand =
    (* m < 2^sb, so m >= hidden_bit (normal) iff bit (sb-1) of m is set. *)
    if Z.testbit m (sb - 1)
    then
      (* normal: biased_exp = (e + sb - 1) + bias; strip the hidden bit. *)
      e + (sb - 1) + bias, Z.sub m hidden_bit
    else
      (* subnormal: biased_exp = 0; m is the bare significand. *)
      0, m
  in
  neg, biased_exp, significand

let pp_smtlib ~eb ~sb ppf = function
  | Plus_infinity -> Fmt.pf ppf "(_ +oo %d %d)" eb sb
  | Minus_infinity -> Fmt.pf ppf "(_ -oo %d %d)" eb sb
  | Plus_zero -> Fmt.pf ppf "(_ +zero %d %d)" eb sb
  | Minus_zero -> Fmt.pf ppf "(_ -zero %d %d)" eb sb
  | NaN -> Fmt.pf ppf "(_ NaN %d %d)" eb sb
  | Finite q ->
    let neg, biased_exp, significand = q_to_bvs ~eb ~sb q in
    (* all-ones exponent is reserved for infinities and NaN *)
    assert (biased_exp < (1 lsl eb) - 1);
    let bfmt n = Fmt.str "%%0%db" n in
    let sign_s = if neg then "1" else "0" in
    let exp_s = Z.format (bfmt eb) (Z.of_int biased_exp) in
    let sig_s = Z.format (bfmt (sb - 1)) significand in
    Fmt.pf ppf "(fp #b%s #b%s #b%s)" sign_s exp_s sig_s

(* (neg, biased_exp, significand) -> rational value *)
let bvs_to_q ~neg ~biased_exp ~mantissa eb sb =
  let bias = bias ~eb in
  let significand_full, exp_shift =
    if biased_exp > 0
    then
      (* normal: significand_full = 2^(sb-1) + mantissa (restore hidden bit),
         exp_shift = biased_exp - bias - (sb-1) (actual_exp - (sb-1)) *)
      Z.add (Z.shift_left Z.one (sb - 1)) mantissa, biased_exp - bias - (sb - 1)
    else
      (* subnormal: significand_full = mantissa (no hidden bit), exp_shift = 1 -
         bias - (sb-1) = -min_exp (fixed actual_exp) *)
      mantissa, -min_exp ~eb ~sb
  in
  (* significand_full * 2^exp_shift *)
  let abs_q =
    if exp_shift >= 0
    then Q.mult_2exp (Q.from_z significand_full) exp_shift
    else Q.div_2exp (Q.from_z significand_full) (-exp_shift)
  in
  if neg then Q.minus abs_q else abs_q

let mk_fp_literal ~neg ~biased_exp ~mantissa ~eb ~sb =
  let max_exp = (1 lsl eb) - 1 in
  (* TODO: these transformations should not be done this early as they can
     affect matching (we are transforming terms received from the parser into
     another representation so the solver does not see the original terms)
     ideally it would be done at the semantic level, with the theory's `make`
     function for example (or something with domains/propagations?) *)
  if biased_exp = max_exp
  then
    (* all-ones exponent: infinity or NaN *)
    if Z.equal mantissa Z.zero
    then if neg then Minus_infinity else Plus_infinity
    else NaN
  else if biased_exp = 0 && Z.equal mantissa Z.zero
  then
    (* zero exponent + zero significand: signed zero *)
    if neg then Minus_zero else Plus_zero
  else Finite (bvs_to_q ~neg ~biased_exp ~mantissa eb sb)

let to_bits ~eb ~sb = function
  | NaN -> None
  | Plus_infinity -> Some (false, (1 lsl eb) - 1, Z.zero)
  | Minus_infinity -> Some (true, (1 lsl eb) - 1, Z.zero)
  | Plus_zero -> Some (false, 0, Z.zero)
  | Minus_zero -> Some (true, 0, Z.zero)
  | Finite q -> Some (q_to_bvs ~eb ~sb q)

(* Largest finite value of the format (eb, sb): 2^emax - 2^(emax - sb). *)
let max_finite_q ~eb ~sb =
  let pow2_q = Fpa_rounding.mult_x_by_2_pow_n Q.one in
  let emax = bias ~eb + 1 in
  Q.sub (pow2_q emax) (pow2_q (emax - sb))

(* Smallest positive normal value: 2^(1 - bias). *)
let min_normal_q ~eb = Fpa_rounding.mult_x_by_2_pow_n Q.one (1 - bias ~eb)

(* [Finite q] is never zero. *)
let is_normal ~eb = function
  | Finite q -> Q.compare (Q.abs q) (min_normal_q ~eb) >= 0
  | Plus_infinity | Minus_infinity | Plus_zero | Minus_zero | NaN -> false

let is_subnormal ~eb = function
  | Finite q -> Q.compare (Q.abs q) (min_normal_q ~eb) < 0
  | Plus_infinity | Minus_infinity | Plus_zero | Minus_zero | NaN -> false

let of_q ?(neg_zero = false) ~eb ~sb mode q =
  if Q.sign q = 0
  then if neg_zero then Minus_zero else Plus_zero
  else
    let neg = Q.sign q < 0 in
    let res, _, _ =
      Fpa_rounding.float_of_rational sb (min_exp ~eb ~sb) mode q
    in
    if Q.sign res = 0
    then if neg then Minus_zero else Plus_zero
    else
      (* [res] has [sb] significant bits, so it overflows iff [|res| >= 2^emax];
         [floor(log2 |res|) <= numbits(num) - numbits(den)] skips computing
         [max_q] in most cases. *)
      let emax = bias ~eb + 1 in
      if Z.numbits (Q.num res) - Z.numbits (Q.den res) < emax
      then Finite res
      else
        let max_q = max_finite_q ~eb ~sb in
        if Q.compare (Q.abs res) max_q <= 0
        then Finite res
        else
          (* Overflow: the result is either an infinity or the largest finite
             value of the right sign, depending on the rounding mode. *)
          let inf = if neg then Minus_infinity else Plus_infinity in
          let max_fin = Finite (if neg then Q.minus max_q else max_q) in
          let module RM = Dolmen.Std.Builtin.Float in
          match (mode : Fpa_rounding.rounding_mode) with
          | RM.RoundNearestTiesToEven | RM.RoundNearestTiesToAway -> inf
          | RM.RoundTowardPositive -> if neg then max_fin else inf
          | RM.RoundTowardNegative -> if neg then inf else max_fin
          | RM.RoundTowardZero -> max_fin

let to_integer mode = function
  | Plus_zero | Minus_zero -> Some Numbers.Z.zero
  | Finite q ->
    Option.map (fun m -> Q.to_z (Fpa_rounding.round_to_integer m q)) mode
  | NaN | Plus_infinity | Minus_infinity -> None

let convert ~eb ~sb mode = function
  | Finite q -> Option.map (fun m -> of_q ~eb ~sb m q) mode
  | (NaN | Plus_infinity | Minus_infinity | Plus_zero | Minus_zero) as v ->
    Some v

(* Evaluation of the SMT-LIB operators, following IEEE 754. *)

let is_negative = function
  | Minus_infinity | Minus_zero -> true
  | Finite q -> Q.sign q < 0
  | Plus_infinity | Plus_zero | NaN -> false

let zero neg = if neg then Minus_zero else Plus_zero

let inf neg = if neg then Minus_infinity else Plus_infinity

let to_q = function
  | Finite q -> Some q
  | Plus_zero | Minus_zero -> Some Q.zero
  | Plus_infinity | Minus_infinity | NaN -> None

let neg = function
  | Plus_infinity -> Minus_infinity
  | Minus_infinity -> Plus_infinity
  | Plus_zero -> Minus_zero
  | Minus_zero -> Plus_zero
  | NaN -> NaN
  | Finite q -> Finite (Q.minus q)

let abs v = if is_negative v then neg v else v

let is_inf = function
  | Plus_infinity | Minus_infinity -> true
  | Plus_zero | Minus_zero | NaN | Finite _ -> false

let is_zero = function
  | Plus_zero | Minus_zero -> true
  | Plus_infinity | Minus_infinity | NaN | Finite _ -> false

(* [round(q)], with [q = a + b] exact and [neg1], [neg2] the signs of [a] and
   [b]. If [q = 0]: [-0] if [a, b < 0], or if their signs differ under RTN. [+0]
   otherwise. *)
let round_sum ~eb ~sb mode q ~neg1 ~neg2 =
  if Q.sign q = 0
  then
    let module RM = Dolmen.Std.Builtin.Float in
    let rtn =
      match (mode : Fpa_rounding.rounding_mode) with
      | RM.RoundTowardNegative -> true
      | RoundNearestTiesToEven | RoundNearestTiesToAway | RoundTowardPositive
      | RoundTowardZero ->
        false
    in
    zero (if Bool.equal neg1 neg2 then neg1 else rtn)
  else of_q ~eb ~sb mode q

(* [round(x + y)]. NaN on NaN or [+oo + -oo]. *)
let add ~eb ~sb mode x y =
  match x, y with
  | NaN, _
  | _, NaN
  | Plus_infinity, Minus_infinity
  | Minus_infinity, Plus_infinity ->
    NaN
  | ((Plus_infinity | Minus_infinity) as v), _
  | _, ((Plus_infinity | Minus_infinity) as v) ->
    v
  | (Plus_zero | Minus_zero | Finite _), (Plus_zero | Minus_zero | Finite _) ->
    let qx = Option.get (to_q x) in
    let qy = Option.get (to_q y) in
    round_sum ~eb ~sb mode (Q.add qx qy) ~neg1:(is_negative x)
      ~neg2:(is_negative y)

(* [x - y = x + (-y)]. *)
let sub ~eb ~sb mode x y = add ~eb ~sb mode x (neg y)

(* [round(x * y)], of sign [sign x xor sign y]. NaN on NaN or [0 * oo]. *)
let mul ~eb ~sb mode x y =
  let neg = not (Bool.equal (is_negative x) (is_negative y)) in
  match x, y with
  | NaN, _ | _, NaN -> NaN
  | _ when (is_inf x && is_zero y) || (is_zero x && is_inf y) -> NaN
  | _ when is_inf x || is_inf y -> inf neg
  | _ when is_zero x || is_zero y -> zero neg
  | _ -> of_q ~eb ~sb mode (Q.mult (Option.get (to_q x)) (Option.get (to_q y)))

(* [round(x / y)], of sign [sign x xor sign y]. NaN on NaN, [0 / 0] or [oo /
   oo], and [x / 0 = oo] and [x / oo = 0]. *)
let div ~eb ~sb mode x y =
  let neg = not (Bool.equal (is_negative x) (is_negative y)) in
  match x, y with
  | NaN, _ | _, NaN -> NaN
  | _ when (is_inf x && is_inf y) || (is_zero x && is_zero y) -> NaN
  | _ when is_inf x || is_zero y -> inf neg
  | _ when is_zero x || is_inf y -> zero neg
  | _ -> of_q ~eb ~sb mode (Q.div (Option.get (to_q x)) (Option.get (to_q y)))

(* [round(x * y + z)], rounded once. NaN on NaN, [0 * oo], or [x * y = +-oo] and
   [z = -+oo]. *)
let fma ~eb ~sb mode x y z =
  let neg_p = not (Bool.equal (is_negative x) (is_negative y)) in
  match x, y, z with
  | NaN, _, _ | _, NaN, _ | _, _, NaN -> NaN
  | _ when (is_inf x && is_zero y) || (is_zero x && is_inf y) -> NaN
  | _ when is_inf x || is_inf y ->
    if is_inf z && not (Bool.equal neg_p (is_negative z))
    then NaN
    else inf neg_p
  | _ when is_inf z -> z
  | _ ->
    let p = Q.mult (Option.get (to_q x)) (Option.get (to_q y)) in
    round_sum ~eb ~sb mode
      (Q.add p (Option.get (to_q z)))
      ~neg1:neg_p ~neg2:(is_negative z)

(* [round(sqrt x)]. NaN on [x < 0], [sqrt(-0) = -0]. With [k = min_exp + 2] and
   [s = isqrt(q * 4^k)]: [sqrt q = s / 2^k] if exact, and otherwise rounds like
   [(2s + 1) / 2^(k+1)], as both are strictly between [s / 2^k] and [(s + 1) /
   2^k], with no rounding boundary (multiple of [2^-(min_exp + 1)]) in
   between. *)
let sqrt ~eb ~sb mode = function
  | (NaN | Plus_zero | Minus_zero | Plus_infinity) as v -> v
  | Minus_infinity -> NaN
  | Finite q when Q.sign q < 0 -> NaN
  | Finite q ->
    let k = min_exp ~eb ~sb + 2 in
    let n = Q.to_z (Q.mult_2exp q (2 * k)) in
    let s = Z.sqrt n in
    let r =
      if Z.equal (Z.mul s s) n
      then Q.div_2exp (Q.from_z s) k
      else Q.div_2exp (Q.from_z (Z.add (Z.shift_left s 1) Z.one)) (k + 1)
    in
    of_q ~eb ~sb mode r

(* [round_int(x)], a zero result has the sign of [x]. The integer can overflow
   in tiny formats, e.g. 3.5 in [(2, 3)]. *)
let round_to_integral ~eb ~sb mode = function
  | Finite q ->
    let r = Fpa_rounding.round_to_integer mode q in
    if Q.sign r = 0 then zero (Q.sign q < 0) else of_q ~eb ~sb mode r
  | (Plus_infinity | Minus_infinity | Plus_zero | Minus_zero | NaN) as v -> v

(* [x = y]: NaN equals nothing, [+0 = -0]. *)
let eq x y =
  match x, y with
  | NaN, _ | _, NaN -> false
  | _ -> (
    match to_q x, to_q y with
    | Some qx, Some qy -> Q.equal qx qy
    | _ -> equal x y)

(* [x < y], false on NaN. *)
let lt x y =
  match x, y with
  | NaN, _ | _, NaN -> false
  | Minus_infinity, Minus_infinity | Plus_infinity, Plus_infinity -> false
  | Minus_infinity, _ | _, Plus_infinity -> true
  | Plus_infinity, _ | _, Minus_infinity -> false
  | _ -> Q.compare (Option.get (to_q x)) (Option.get (to_q y)) < 0

(* [x <= y]. *)
let le x y = lt x y || eq x y

(* [min(x, y)] or [max(x, y)], NaN only if both are NaN. [None] on [+0] and
   [-0]: either may be returned. *)
let min_max ~is_min x y =
  match x, y with
  | NaN, v | v, NaN -> Some v
  | _ when is_zero x && is_zero y && not (equal x y) -> None
  | _ when Bool.equal (lt x y) is_min -> Some x
  | _ -> Some y

let min = min_max ~is_min:true

let max = min_max ~is_min:false

(* [x - y * n], [n = round_ne(x / y)], exact; a zero result has the sign of [x].
   NaN on NaN, [x = +-oo] or [y = +-0]; [x] if [y = +-oo] or [x = +-0]. *)
let rem ~eb ~sb x y =
  match x, y with
  | (NaN | Plus_infinity | Minus_infinity), _ -> NaN
  | _, (NaN | Plus_zero | Minus_zero) -> NaN
  | (Finite _ | Plus_zero | Minus_zero), (Plus_infinity | Minus_infinity)
  | (Plus_zero | Minus_zero), Finite _ ->
    x
  | Finite qx, Finite qy ->
    let rne = Dolmen.Std.Builtin.Float.RoundNearestTiesToEven in
    let n = Fpa_rounding.round_to_integer rne (Q.div qx qy) in
    let neg_zero = Q.sign qx < 0 in
    of_q ~neg_zero ~eb ~sb rne Q.(sub qx (mult qy n))
