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

(* This works because we know that [q] is always dyadic since its created from
   an SMT-LIB float literal. *)
let hex_of_q q =
  let sign = if Q.sign q < 0 then "-" else "" in
  let num = Z.abs (Q.num q) in
  let k = Z.numbits (Q.den q) - 1 in
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
let q_to_bvs eb sb q =
  let bias = fp_bias eb in
  let min_exp = fp_min_exp eb sb in
  let neg = Q.sign q < 0 in
  (* (_, m, e) with m*2^e = |q|, e = max(floor(log2|q|) + 1 - sb, -min_exp). *)
  let _, m, e =
    Fpa_rounding.float_of_rational sb min_exp Fpa_rounding.NearestTiesToEven
      (Q.abs q)
  in
  (* hidden_bit = 2^(sb-1), m >= hidden_bit -> normal *)
  let hidden_bit = Z.shift_left Z.one (sb - 1) in
  let biased_exp, significand =
    if Z.compare m hidden_bit >= 0
    then
      (* normal: biased_exp = (e + sb - 1) + bias; strip the hidden bit. *)
      e + (sb - 1) + bias, Z.sub m hidden_bit
    else
      (* subnormal: biased_exp = 0; m is the bare significand. *)
      0, m
  in
  neg, biased_exp, significand

let pp_smtlib eb sb ppf = function
  | Plus_infinity -> Fmt.pf ppf "(_ +oo %d %d)" eb sb
  | Minus_infinity -> Fmt.pf ppf "(_ -oo %d %d)" eb sb
  | Plus_zero -> Fmt.pf ppf "(_ +zero %d %d)" eb sb
  | Minus_zero -> Fmt.pf ppf "(_ -zero %d %d)" eb sb
  | NaN -> Fmt.pf ppf "(_ NaN %d %d)" eb sb
  | Finite q ->
    let neg, biased_exp, significand = q_to_bvs eb sb q in
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

let mk_fp_literal ~neg ~biased_exp ~mantissa ~e ~s =
  let max_exp = (1 lsl e) - 1 in
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
  else Finite (bvs_to_q ~neg ~biased_exp ~mantissa e s)
