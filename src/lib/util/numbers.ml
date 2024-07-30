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

module Z = struct
  type t = Z.t

  let zero           = Z.zero
  let one            = Z.one
  let m_one          = Z.minus_one

  let compare a b    = Z.compare a b
  let compare_to_0 t = Z.sign t
  let equal   a b    = Z.equal a b
  let sign t         = Z.sign t
  let hash t         = Z.hash t

  let is_zero t      = compare_to_0 t = 0
  let is_one  t      = equal t one
  let is_m_one t     = equal t m_one

  let add a b     = Z.add a b
  let sub a b     = Z.sub a b
  let mult a b    = Z.mul a b
  let div a b     = assert (not (is_zero b)); Z.div a b
  let rem a b     = assert (not (is_zero b)); Z.rem a b
  let div_rem a b = assert (not (is_zero b)); Z.div_rem a b
  let minus t     = Z.neg t
  let abs t       = Z.abs t
  let max t1 t2   = Z.max t1 t2
  let from_int n    = Z.of_int n
  let from_string s = Z.of_string s
  let to_string t   = Z.to_string t
  let print fmt z   = Format.fprintf fmt "%s" (to_string z)
  let pp_print = Z.pp_print

  let my_gcd a b =
    if is_zero a then b
    else if is_zero b then a
    else Z.gcd a b

  let my_lcm a b =
    try
      let res1 = Z.lcm a b in
      assert (equal res1 (div (mult a b) (my_gcd a b)));
      res1
    with Division_by_zero -> assert false

  let to_machine_int t =
    try Some (Z.to_int t) with Z.Overflow -> None

  (* These functuons are not exported, but they are used by module Q below *)
  let to_float z = Z.to_float z
  let fdiv z1 z2 = assert (not (is_zero z2)); Z.fdiv z1 z2
  let cdiv z1 z2 = assert (not (is_zero z2)); Z.cdiv z1 z2
  let power z n  =
    assert (n >= 0);
    Z.pow z n

  (* Shifts left by (n:int >= 0) bits. This is the same as t * pow(2,n) *)
  let shift_left = Z.shift_left

  (* returns sqrt truncated with the remainder. It assumes that the argument
     is positive, otherwise, [Invalid_argument] is raised. *)
  let sqrt_rem = Z.sqrt_rem

  let testbit z n =
    assert (n >= 0);
    Z.testbit z n

  let numbits = Z.numbits

end

module Q = struct
  exception Not_a_float

  type t = Q.t

  let num t  = Q.num t
  let den t  = Q.den t

  let zero   = Q.zero
  let one    = Q.one
  let m_one  = Q.minus_one

  let compare t1 t2  = Q.compare t1 t2
  let compare_to_0 t = Q.sign t
  let equal t1 t2    = Q.equal t1 t2
  let sign t         = Q.sign t
  let hash t         = 13 * Z.hash (num t) + 23 * Z.hash (den t)

  let is_zero t  = compare_to_0 t = 0
  let is_one  t  = equal t one
  let is_m_one t = equal t m_one
  let is_int t   = Z.is_one (den t)

  let add t1 t2  = Q.add t1 t2
  let sub t1 t2  = Q.sub t1 t2
  let mult t1 t2 = Q.mul t1 t2
  let div t1 t2  = assert (not (is_zero t2)); Q.div t1 t2
  let minus t    = Q.neg t
  let abs t      = Q.abs t
  let min t1 t2  = Q.min t1 t2
  let max t1 t2  = Q.max t1 t2

  let inv t      =
    if Z.is_zero (num t) then raise Division_by_zero;
    Q.inv t

  let from_int n    = Q.of_int n
  let from_z z      = Q.make z Z.one
  let from_zz z1 z2 = Q.make z1 z2
  let from_string s = Q.of_string s
  let from_float f  =
    if Float.(equal f infinity || equal f neg_infinity) then raise Not_a_float;
    Q.of_float f

  let to_string t = Q.to_string t
  let to_z q      = assert (is_int q); num q
  let to_float t  = (Z.to_float (num t)) /. (Z.to_float (den t))
  let print fmt q = Format.fprintf fmt "%s" (to_string q)

  let floor t      = from_z (Z.fdiv (num t) (den t))
  let ceiling t    = from_z (Z.cdiv (num t) (den t))
  let power t n    =
    let abs_n = Stdlib.abs n in
    let num_pow = Z.power (num t) abs_n in
    let den_pow = Z.power (den t) abs_n in
    if n >= 0 then from_zz num_pow den_pow else from_zz den_pow num_pow

  let modulo t1 t2 =
    assert (is_int t1 && is_int t2);
    from_zz (Z.rem (num t1) (num t2)) Z.one

  (* converts the argument to an integer by truncation. *)
  let truncate = Q.to_bigint

  let mult_2exp = Q.mul_2exp

  let div_2exp = Q.div_2exp

  let two = from_int 2

  let root_num q n =
    assert (n >= 0);
    let sgn = sign q in
    assert (sgn >= 0);
    if n = 1 then Some q
    else
    if sgn = 0 then Some zero
    else
      let v = to_float q in
      let w =
        if (Float.compare v min_float) < 0 then min_float
        else if (Float.compare v max_float) > 0 then max_float
        else v
      in
      let flt = if n = 2 then sqrt w else w ** (1. /. float n) in
      match classify_float flt with
      | FP_normal | FP_subnormal | FP_zero -> Some (from_float flt)
      | FP_infinite | FP_nan -> None

  let unaccurate_root_default q n =
    match root_num q n with
    | None -> None
    | (Some s) as res ->
      let d = sub q (power s n) in
      if sign d >= 0 then res else Some (div q (power s (n - 1)))

  let unaccurate_root_excess q n =
    match root_num q n with
    | None -> None
    | Some s as res ->
      let d = sub q (power s n) in
      if sign d <= 0 then res else Some (div q (power s (n - 1)))


  let accurate_root_default q n =
    let dd = unaccurate_root_default q n in
    let ee = unaccurate_root_excess  q n in
    match dd, ee with
    | None, _ | _ , None -> dd
    | Some d, Some e ->
      let cand = div (add d e) two in
      if Q.compare (power cand n) q <= 0 then Some cand else dd

  let accurate_root_excess q n =
    let dd = unaccurate_root_default q n in
    let ee = unaccurate_root_excess  q n in
    match dd, ee with
    | None, _ | _ , None -> ee
    | Some d, Some e ->
      let cand = div (add d e) two in
      if Q.compare (power cand n) q >= 0 then Some cand else ee


  let sqrt_excess q =
    match root_num q 2 with
    | None -> None
    | Some s ->
      if not (is_zero s) then Some (div (add s (div q s)) two)
      else accurate_root_default q 2

  let sqrt_default q =
    match sqrt_excess q with
    | None -> None
    | Some s ->
      if not (is_zero s) then Some (div q s)
      else accurate_root_excess q 2

  let root_default = accurate_root_default
  let root_excess  = accurate_root_excess
end
