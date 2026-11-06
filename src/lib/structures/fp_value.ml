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
let fp_bias eb = (1 lsl (eb - 1)) - 1

(* min_exp = bias + sb - 2 *)
let fp_min_exp eb sb = fp_bias eb + sb - 2

(* rational value -> (neg, biased_exp, significand) *)
let q_to_bvs ~eb ~sb q =
  let bias = fp_bias eb in
  let min_exp = fp_min_exp eb sb in
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
  let bias = fp_bias eb in
  let significand_full, exp_shift =
    if biased_exp > 0
    then
      (* normal: significand_full = 2^(sb-1) + mantissa (restore hidden bit),
         exp_shift = biased_exp - bias - (sb-1) (actual_exp - (sb-1)) *)
      Z.add (Z.shift_left Z.one (sb - 1)) mantissa, biased_exp - bias - (sb - 1)
    else
      (* subnormal: significand_full = mantissa (no hidden bit), exp_shift = 1 -
         bias - (sb-1) = -min_exp (fixed actual_exp) *)
      mantissa, -fp_min_exp eb sb
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
  let emax = fp_bias eb + 1 in
  Q.sub (pow2_q emax) (pow2_q (emax - sb))

(* Smallest positive normal value: 2^(1 - bias). *)
let min_normal_q ~eb = Fpa_rounding.mult_x_by_2_pow_n Q.one (1 - fp_bias eb)

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
      Fpa_rounding.float_of_rational sb (fp_min_exp eb sb) mode q
    in
    if Q.sign res = 0
    then if neg then Minus_zero else Plus_zero
    else
      (* [res] has [sb] significant bits, so it overflows iff [|res| >= 2^emax];
         [floor(log2 |res|) <= numbits(num) - numbits(den)] skips computing
         [max_q] in most cases. *)
      let emax = fp_bias eb + 1 in
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
