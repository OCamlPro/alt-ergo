(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2017   --   INRIA - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

open Big_int

type t = big_int(*
let compare = compare_big_int*)

let zero = zero_big_int(*
let one = unit_big_int
let of_int = big_int_of_int

let succ = succ_big_int
let pred = pred_big_int
                 *)
let add_int = add_int_big_int
let mul_int = mult_int_big_int(*

let add = add_big_int
let sub = sub_big_int
let mul = mult_big_int
let minus = minus_big_int

let sign = sign_big_int

let eq = eq_big_int
let lt = lt_big_int
let gt = gt_big_int
let le = le_big_int
let ge = ge_big_int

let euclidean_div_mod x y =
  if sign y = 0 then zero, zero else quomod_big_int x y

let euclidean_div x y = fst (euclidean_div_mod x y)
let euclidean_mod x y = snd (euclidean_div_mod x y)

let computer_div_mod x y =
  let (q,r) as qr = euclidean_div_mod x y in
  (* when y <> 0, we have x = q*y + r with 0 <= r < |y| *)
  if sign x >= 0 || sign r = 0 then qr
  else
    if sign y < 0
    then (pred q, add r y)
    else (succ q, sub r y)

let computer_div x y = fst (computer_div_mod x y)
let computer_mod x y = snd (computer_div_mod x y)

let min = min_big_int
let max = max_big_int
let abs = abs_big_int

let num_digits = num_digits_big_int

let pow_int_pos = power_int_positive_int
let pow_int_pos_bigint = power_int_positive_big_int

let to_string = string_of_big_int
let of_string = big_int_of_string
let to_int = int_of_big_int*)
