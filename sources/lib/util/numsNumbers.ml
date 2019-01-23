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
module Z : NumbersInterface.ZSig with type t = Big_int.big_int = struct

  open Big_int

  type t = big_int

  let zero = zero_big_int
  let one = unit_big_int
  let m_one = minus_big_int one

  let compare a b = compare_big_int a b
  let compare_to_0 a = sign_big_int a
  let equal a b = eq_big_int a b

  let is_zero t = compare_to_0 t = 0
  let is_one  t = equal t one
  let is_m_one t = equal t m_one
  let sign t = sign_big_int t
  let hash t = Hashtbl.hash t

  let add a b = add_big_int a b
  let mult a b = mult_big_int a b
  let abs t = abs_big_int t
  let sub a b = sub_big_int a b
  let minus t = minus_big_int t
  let div a b = assert (not (is_zero b)); div_big_int a b
  let max a b = max_big_int a b

  let to_string t = string_of_big_int t
  let from_string s = big_int_of_string s
  let from_int n = big_int_of_int n
  let rem a b = assert (not (is_zero b)); mod_big_int a b
  let div_rem a b = assert (not (is_zero b)); quomod_big_int a b
  let print fmt t = Format.fprintf fmt "%s" (to_string t)

  let my_gcd a b =
    if is_zero a then b
    else if is_zero b then a
    else gcd_big_int a b

  let my_lcm a b =
    try div (mult a b) (my_gcd a b)
    with e ->
      Format.printf "my_lcm %a %a failed with:@.%s@."
        print a print b (Printexc.to_string e);
      assert false

  let to_float t = float_of_big_int t

  let to_machine_int t =
    try Some (Big_int.int_of_big_int t) with _ -> None

  let fdiv a b =
    assert (not (is_zero b));
    let open Num in
    try
      let n1 = num_of_big_int a in
      let n2 = num_of_big_int b in
      let nm = div_num n1 n2 in
      big_int_of_num (floor_num nm)
    with e ->
      Format.printf "fdiv %a %a failed with:@.%s@."
        print a print b (Printexc.to_string e);
      assert false

  let cdiv a b =
    assert (not (is_zero b));
    let open Num in
    try
      let n1 = num_of_big_int a in
      let n2 = num_of_big_int b in
      let nm = div_num n1 n2 in
      big_int_of_num (ceiling_num nm)
    with e ->
      Format.printf "cdiv %a %a failed with:@.%s@."
        print a print b (Printexc.to_string e);
      assert false

  let power a n =
    assert (n>=0);
    power_big_int_positive_int a n

  (* Shifts left by (n:int >= 0) bits. This is the same as t * pow(2,n) *)
  let shift_left = shift_left_big_int

  (* returns sqrt truncated with the remainder. It assumes that the argument
     is positive, otherwise, [Invalid_argument] is raised. *)
  let sqrt_rem t =
    let sq = sqrt_big_int t in
    sq, sub t (mult sq sq)

  let testbit z n =
    assert (n >= 0);
    is_one (extract_big_int z n 1)

  let numbits = Big_int.num_bits_big_int

end


(** Rationals implementation. Based on Zarith's rationals **)
module Q : NumbersInterface.QSig with module Z = Z = struct

  module Z = Z
  exception Not_a_float

  open Num

  type t = num

  let zero = Int 0
  let one = Int 1
  let m_one = Int (-1)
  let of_int n = Int n
  let compare_to_0 n = sign_num n
  let is_zero n = compare_to_0 n = 0
  let equal a b = a =/ b
  let is_one n = equal one n
  let is_m_one n = equal m_one n
  let ceiling = ceiling_num
  let floor = floor_num
  let is_int = is_integer_num
  let abs = abs_num

  let power a n =
    if n = 0 then one (* 0 ^ 0 = 1, undefined in mathematics*)
    else match a with
      | Int 1 -> one
      | Int 0 -> zero
      | Int (-1) ->
        if n mod 2 = 0 then one else m_one
      | _ -> power_num a (Int n)

  let modulo = mod_num
  let div a b = assert (not (is_zero b)); div_num a b
  let mult = mult_num
  let sub = sub_num
  let add = add_num
  let minus = minus_num
  let sign = sign_num
  let compare = compare_num
  let equal a b = a =/ b

  let to_string = string_of_num
  let from_string = num_of_string
  let to_float = float_of_num
  let to_z = big_int_of_num
  let from_z  = num_of_big_int

  let from_int i = num_of_int i

  let den = function
    | Int _ | Big_int _ -> Big_int.unit_big_int
    | Ratio rat -> Ratio.denominator_ratio rat

  let num = function
    | Int i -> Big_int.big_int_of_int i
    | Big_int b -> b
    | Ratio rat -> Ratio.numerator_ratio rat

  let from_float x =
    if x = infinity || x = neg_infinity then raise Not_a_float;
    let (f, n) = frexp x in
    let z =
      Big_int.big_int_of_string
        (Int64.to_string (Int64.of_float (f *. 2. ** 52.))) in
    let factor = power (of_int 2) (n - 52) in
    mult (from_z z) factor

  let hash v = match v with
    | Int i -> i
    | Big_int b -> Hashtbl.hash b
    | Ratio rat -> Hashtbl.hash (Ratio.normalize_ratio rat)

  let print fmt q = Format.fprintf fmt "%s" (to_string q)

  let min t1 t2  = min_num t1 t2
  let max t1 t2  = max_num t1 t2

  let inv t =
    if Z.is_zero (num t) then raise Division_by_zero;
    one // t

  let from_zz z1 z2 = Big_int z1 // Big_int z2

  (********
           comparer avec l'implem de Alain de of_float
           let ratio_of_float f =
           Ratio.ratio_of_string (string_of_float f)

           let num_of_float f = num_of_ratio (ratio_of_float f)

           let of_float x =
           let res = of_float x in
           let z = num_of_float x in
           assert (res =/ z);
           res
   ********)

  let truncate t =
    let res = integer_num t in
    assert (compare (abs res) (abs t) <= 0);
    match res with
    | Int i -> Big_int.big_int_of_int i
    | Big_int b -> b
    | Ratio _ -> assert false

  let mult_2exp t n = mult t (power (Int 2) n)

  let div_2exp t n = div t (power (Int 2) n)

end

