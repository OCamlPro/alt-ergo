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

module Sy = Symbols
module Hs = Hstring
module E = Expr

module Q = Numbers.Q
module Z = Numbers.Z

let fpa_rounding_mode = Ty.Text ([], Hs.make "fpa_rounding_mode")

(** Helper functions **)

let mult_x_by_2_pow_n x n =
  (* Q.mul_2exp does not support negative i according to Cody ? *)
  let res1 = if n >= 0 then Q.mult_2exp x n else Q.div_2exp x (-n) in
  let res2 = Q.mult res1 Q.one in (* Bug in Zarith according to Cody ? *)
  assert (Q.equal res1 res2);
  res2

let div_x_by_2_pow_n x n = mult_x_by_2_pow_n x (-n)

let two = Q.from_int 2

let half = Q.div Q.one two

(* Integer part of binary logarithm for NON-ZERO POSITIVE number *)
let integer_log_2 =
  let rec aux m e =
    if Q.compare m two >= 0 then aux (div_x_by_2_pow_n m 1) (e+1)
    else
    if Q.compare m Q.one >= 0 then e
    else
      let () = assert (Q.compare_to_0 m > 0) in
      aux (mult_x_by_2_pow_n m 1) (e - 1)
  in
  fun m ->
    if Q.compare_to_0 m <= 0 then
      begin
        Printer.print_err
          "integer_log_2 not defined for input (%a)" Q.print m;
        assert false
      end;
    let res = aux m 0 in
    (* Printer.print_dbg
       "found that integer_log_2 of %a is %d" Q.print m res;*)
    assert (Q.compare (mult_x_by_2_pow_n Q.one res) m <= 0);
    assert (Q.compare (mult_x_by_2_pow_n Q.one (res+1)) m > 0);
    res

let signed_one y =
  let tmp = Q.sign y in
  assert (tmp <> 0);
  if tmp > 0 then Z.one else Z.m_one


let round_big_int (mode : Sy.rounding_mode) y =
  match mode with
  | Up     -> Q.num (Q.ceiling y)
  | Down   -> Q.num (Q.floor y)
  | ToZero -> Q.truncate y

  | NearestTiesToEven ->
    let z = Q.truncate y in
    let diff = Q.abs (Q.sub y (Q.from_z z)) in
    if Q.sign diff = 0 then z
    else
      let tmp = Q.compare diff half in
      if tmp < 0 then z
      else if tmp > 0 then Z.add z (signed_one y)
      else if Z.testbit z 0 then Z.add z (signed_one y)
      else z

  | NearestTiesToAway ->
    let z = Q.truncate y in
    let diff = Q.abs (Q.sub y (Q.from_z z)) in
    if Q.sign diff = 0 then z
    else if Q.compare diff half < 0 then z else Z.add z (signed_one y)

  | Aw | Od | No | Nz | Nd | Nu -> assert false


let to_mantissa_exp prec exp mode x =
  let sign_x = Q.sign x in
  assert ((sign_x = 0) == Q.equal x Q.zero);
  if sign_x = 0 then Z.zero, 1
  else
    let abs_x = Q.abs x in
    let e = integer_log_2 abs_x in
    let e' = max (e + 1 - prec) (- exp) in
    let y = mult_x_by_2_pow_n x (-e') in
    let r_y = round_big_int mode y in
    r_y, e'

module MQ =
  Map.Make (struct
    type t = int * int * Sy.rounding_mode * Q.t
    let compare (prec1, exp1, mode1, x1) (prec2, exp2, mode2, x2) =
      let c = Q.compare x1 x2 in
      if c <> 0 then c
      else
        let c = prec1 - prec2 in
        if c <> 0 then c
        else
          let c = exp1 - exp2 in
          if c <> 0 then c
          else Stdlib.compare mode1 mode2
  end)

let cache = ref MQ.empty

(* Compute the floating-point approximation of a rational number *)
let float_of_rational prec exp mode x =
  (* prec = 24 and exp = 149 for 32 bits (or exp = -149 ???) *)
  let input = (prec, exp, mode, x) in
  try MQ.find input !cache
  with Not_found ->
    let m, e = to_mantissa_exp prec exp mode x in
    let res = mult_x_by_2_pow_n (Q.from_z m) e in
    cache := MQ.add input (res, m, e) !cache;
    res, m, e

let round_to_integer mode q =
  Q.from_z (round_big_int (E.rounding_mode_view mode) q)

let empty_cache () =
  cache := MQ.empty
