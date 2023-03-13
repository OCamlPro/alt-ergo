(******************************************************************************)
(*                                                                            *)
(*     The Alt-Ergo theorem prover                                            *)
(*     Copyright (C) 2006-2013                                                *)
(*                                                                            *)
(*     Sylvain Conchon                                                        *)
(*     Evelyne Contejean                                                      *)
(*                                                                            *)
(*     Francois Bobot                                                         *)
(*     Mohamed Iguernelala                                                    *)
(*     Stephane Lescuyer                                                      *)
(*     Alain Mebsout                                                          *)
(*                                                                            *)
(*     CNRS - INRIA - Universite Paris Sud                                    *)
(*                                                                            *)
(*     This file is distributed under the terms of the Apache Software        *)
(*     License version 2.0                                                    *)
(*                                                                            *)
(*  ------------------------------------------------------------------------  *)
(*                                                                            *)
(*     Alt-Ergo: The SMT Solver For Software Verification                     *)
(*     Copyright (C) 2013-2018 --- OCamlPro SAS                               *)
(*                                                                            *)
(*     This file is distributed under the terms of the Apache Software        *)
(*     License version 2.0                                                    *)
(*                                                                            *)
(******************************************************************************)

(** Integers implementation. Based on Zarith's integers **)
module Z : Numbers_interface.ZSig with type t = Z.t = struct

  type t = Z.t

  let zero = Z.zero
  let one = Z.one
  let m_one = Z.minus_one

  let compare = Z.compare
  let compare_to_0 = Z.sign
  let equal = Z.equal
  let sign = Z.sign
  let hash = Z.hash

  let is_zero t = compare_to_0 t = 0
  let is_one t = equal t one
  let is_m_one t = equal t m_one

  let add = Z.add
  let sub = Z.sub
  let mult = Z.mul
  let div a b = assert (not (is_zero b)); Z.div a b
  let rem a b = assert (not (is_zero b)); Z.rem a b
  let div_rem a b = assert (not (is_zero b)); Z.div_rem a b
  let minus = Z.neg
  let abs = Z.abs
  let max = Z.max
  let from_int = Z.of_int
  let from_string = Z.of_string
  let to_string = Z.to_string
  let print fmt z = Format.fprintf fmt "%s" (to_string z)

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


(** Rationals implementation. Based on Zarith's rationals **)
module Q: Numbers_interface.QSig with module Z = Z = struct

  module Z = Z
  exception Not_a_float

  type t = Q.t

  let num = Q.num
  let den = Q.den

  let zero = Q.zero
  let one = Q.one
  let m_one = Q.minus_one

  let compare = Q.compare
  let compare_to_0 = Q.sign
  let equal = Q.equal
  let sign = Q.sign
  let hash t = 13 * Z.hash (num t) + 23 * Z.hash (den t)

  let is_zero t = compare_to_0 t = 0
  let is_one t = equal t one
  let is_m_one t = equal t m_one
  let is_int t = Z.is_one (den t)

  let add = Q.add
  let sub  = Q.sub
  let mult = Q.mul
  let div t1 t2 = assert (not (is_zero t2)); Q.div t1 t2
  let minus = Q.neg
  let abs = Q.abs
  let min = Q.min
  let max = Q.max

  let inv t =
    if Z.is_zero (num t) then raise Division_by_zero;
    Q.inv t

  let from_int = Q.of_int
  let from_z z = Q.make z Z.one
  let from_zz = Q.make
  let from_string = Q.of_string
  let from_float f  =
    if f = infinity || f = neg_infinity then raise Not_a_float;
    Q.of_float f

  let to_string = Q.to_string
  let to_z q = assert (is_int q); num q
  let to_float t = (Z.to_float (num t)) /. (Z.to_float (den t))
  let print fmt q = Format.fprintf fmt "%s" (to_string q)

  let floor t = from_z (Z.fdiv (num t) (den t))
  let ceiling t = from_z (Z.cdiv (num t) (den t))
  let power t n =
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

end
