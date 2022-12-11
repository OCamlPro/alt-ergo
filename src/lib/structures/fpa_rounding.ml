(******************************************************************************)
(*                                                                            *)
(*     Alt-Ergo: The SMT Solver For Software Verification                     *)
(*     Copyright (C) 2013-2018 --- OCamlPro SAS                               *)
(*                                                                            *)
(*     This file is distributed under the terms of the license indicated      *)
(*     in the file 'License.OCamlPro'. If 'License.OCamlPro' is not           *)
(*     present, please contact us to clarify licensing.                       *)
(*                                                                            *)
(******************************************************************************)

module Sy = Symbols
module Hs = Hstring
module E = Expr

module Q = Numbers.Q
module Z = Numbers.Z

let is_rounding_mode t =
  Options.get_use_fpa() &&
  match t with
  | { E.ty = Ty.Tsum {name; _}; _ } ->
    String.compare (Hs.view name) "fpa_rounding_mode" = 0
  | _ -> false

let fpa_rounding_mode =
  let name = Hs.make "fpa_rounding_mode" in
  let constrs =
    [ (* standards *)
      Hs.make "NearestTiesToEven";
      Hs.make "NearestTiesToAway";
      Hs.make "ToZero";
      Hs.make "Up";
      Hs.make "Down";
      (* non standards *)
      Hs.make "Aw";
      Hs.make "Od";
      Hs.make "Nodd";
      Hs.make "Nz";
      Hs.make "Nd";
      Hs.make "Nu" ]
  in
  Ty.Tsum {name; constrs}

(*  why3/standard rounding modes*)

let _NearestTiesToEven__rounding_mode =
  E.mk_term (Sy.constr "NearestTiesToEven") []
    fpa_rounding_mode
(** ne in Gappa: to nearest, tie breaking to even mantissas*)

let _ToZero__rounding_mode =
  E.mk_term (Sy.constr "ToZero") [] fpa_rounding_mode
(** zr in Gappa: toward zero *)

let _Up__rounding_mode =
  E.mk_term (Sy.constr "Up") [] fpa_rounding_mode
(** up in Gappa: toward plus infinity *)

let _Down__rounding_mode =
  E.mk_term (Sy.constr "Down") [] fpa_rounding_mode
(** dn in Gappa: toward minus infinity *)

let _NearestTiesToAway__rounding_mode =
  E.mk_term (Sy.constr "NearestTiesToAway") []
    fpa_rounding_mode
(** na : to nearest, tie breaking away from zero *)

(* additional Gappa rounding modes *)

let _Aw__rounding_mode =
  E.mk_term (Sy.constr "Aw") [] fpa_rounding_mode
(** aw in Gappa: away from zero **)

let _Od__rounding_mode =
  E.mk_term (Sy.constr "Od") [] fpa_rounding_mode
(** od in Gappa: to odd mantissas *)

let _No__rounding_mode =
  E.mk_term (Sy.constr "No") [] fpa_rounding_mode
(** no in Gappa: to nearest, tie breaking to odd mantissas *)

let _Nz__rounding_mode =
  E.mk_term (Sy.constr "Nz") [] fpa_rounding_mode
(** nz in Gappa: to nearest, tie breaking toward zero *)

let _Nd__rounding_mode =
  E.mk_term (Sy.constr "Nd") [] fpa_rounding_mode
(** nd in Gappa: to nearest, tie breaking toward minus infinity *)

let _Nu__rounding_mode =
  E.mk_term (Sy.constr "Nu") [] fpa_rounding_mode
(** nu in Gappa: to nearest, tie breaking toward plus infinity *)


(** Hepler functions **)

let mult_x_by_2_pow_n x n =
  (* Q.mul_2exp does not support negative i according to Cody ? *)
  let res1 = if n >= 0 then Q.mult_2exp x n else Q.div_2exp x (-n) in
  let res2 = Q.mult res1 Q.one in (* Bug in Zarith according to Cody ? *)
  assert (Q.equal res1 res2);
  res2

let div_x_by_2_pow_n x n = mult_x_by_2_pow_n x (-n)

let two = Q.from_int 2

let half = Q.div Q.one two

type rounding_mode =
  (* five standard/why3 fpa rounding modes *)
  | NearestTiesToEven
  (*ne in Gappa: to nearest, tie breaking to even mantissas*)
  | ToZero (* zr in Gappa: toward zero *)
  | Up (* up in Gappa: toward plus infinity *)
  | Down (* dn in Gappa: toward minus infinity *)
  | NearestTiesToAway (* na : to nearest, tie breaking away from zero *)

  (* additional Gappa rounding modes *)
  | Aw (* aw in Gappa: away from zero **)
  | Od (* od in Gappa: to odd mantissas *)
  | No (* no in Gappa: to nearest, tie breaking to odd mantissas *)
  | Nz (* nz in Gappa: to nearest, tie breaking toward zero *)
  | Nd (* nd in Gappa: to nearest, tie breaking toward minus infinity *)
  | Nu (* nu in Gappa: to nearest, tie breaking toward plus infinity *)

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


let round_big_int mode y =
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

let mode_of_term t =
  let eq_t s = E.equal s t in
  if eq_t _NearestTiesToEven__rounding_mode then NearestTiesToEven
  else if eq_t _ToZero__rounding_mode then ToZero
  else if eq_t _Up__rounding_mode then Up
  else if eq_t _Down__rounding_mode then Down
  else if eq_t _NearestTiesToAway__rounding_mode then NearestTiesToAway
  else if eq_t _Aw__rounding_mode then Aw
  else if eq_t _Od__rounding_mode then Od
  else if eq_t _No__rounding_mode then No
  else if eq_t _Nz__rounding_mode then Nz
  else if eq_t _Nd__rounding_mode then Nd
  else if eq_t _Nu__rounding_mode then Nu
  else
    begin
      Printer.print_err "bad rounding mode %a" E.print t;
      assert false
    end

let int_of_term (t : E.t) =
  match t with
  | { top_sy = Sy.Int n; _ } ->
    let n = Hstring.view n in
    let n =
      try int_of_string n
      with _ ->
        Printer.print_err
          "error when trying to convert %s to an int" n;
        assert false
    in
    n (* ! may be negative or null *)
  | _ as t ->
    Printer.print_err
      "The given term %a is not an integer" E.print t;
    assert false

module MQ =
  Map.Make (struct
    type t = E.t * E.t * E.t * Q.t
    let compare (prec1, exp1, mode1, x1) (prec2, exp2, mode2, x2) =
      let c = Q.compare x1 x2 in
      if c <> 0 then c
      else
        let c = E.compare prec1 prec2 in
        if c <> 0 then c
        else
          let c = E.compare exp1 exp2 in
          if c <> 0 then c
          else E.compare mode1 mode2
  end)

let cache = ref MQ.empty

(* Compute the floating-point approximation of a rational number *)
let float_of_rational prec exp mode x =
  (* prec = 24 and exp = 149 for 32 bits (or exp = -149 ???) *)
  let input = (prec, exp, mode, x) in
  try MQ.find input !cache
  with Not_found ->
    let mode = mode_of_term mode in
    let prec = int_of_term prec in
    let exp  = int_of_term exp in
    let m, e = to_mantissa_exp prec exp mode x in
    let res = mult_x_by_2_pow_n (Q.from_z m) e in
    cache := MQ.add input (res, m, e) !cache;
    res, m, e

let round_to_integer mode q =
  Q.from_z (round_big_int (mode_of_term mode) q)

[@@ocaml.ppwarning "TODO: Change Symbols.Float to store FP numeral \
                    constants (eg, <24, -149> for single) instead of \
                    having terms"]
let make_adequate_app s l ty =
  match s with
  | Sy.Name (hs, Sy.Other) when Options.get_use_fpa() ->
    let s, l  =
      match Hstring.view hs, l with
      | "float", [_;_;_;_] -> Sy.Op Sy.Float, l
      | "float32", [_;_;] -> Sy.Op Sy.Float,(E.int "24")::(E.int "149")::l
      | "float32d", [_] ->
        Sy.Op Sy.Float,
        (E.int "24")::
        (E.int "149")::
        _NearestTiesToEven__rounding_mode :: l

      | "float64", [_;_;] -> Sy.Op Sy.Float,(E.int "53")::(E.int "1074")::l
      | "float64d", [_] ->
        Sy.Op Sy.Float,
        (E.int "53")::
        (E.int "1074")::
        _NearestTiesToEven__rounding_mode :: l

      | "integer_round", [_;_] -> Sy.Op Sy.Integer_round, l

      | "fixed", [_;_;_;_] -> Sy.Op Sy.Fixed, l
      | "sqrt_real", [_] -> Sy.Op Sy.Sqrt_real, l
      | "sqrt_real_default", [_] -> Sy.Op Sy.Sqrt_real_default, l
      | "sqrt_real_excess", [_] -> Sy.Op Sy.Sqrt_real_excess, l
      | "abs_int", [_] ->  Sy.Op Sy.Abs_int, l
      | "abs_real", [_] ->  Sy.Op Sy.Abs_real, l
      | "real_of_int", [_] -> Sy.Op Sy.Real_of_int, l
      | "int_floor", [_] -> Sy.Op Sy.Int_floor, l
      | "int_ceil", [_] -> Sy.Op Sy.Int_ceil, l
      | "max_real", [_;_] -> Sy.Op Sy.Max_real, l
      | "max_int", [_;_] -> Sy.Op Sy.Max_int, l
      | "min_real", [_;_] -> Sy.Op Sy.Min_real, l
      | "min_int", [_;_] -> Sy.Op Sy.Min_int, l
      | "integer_log2", [_] -> Sy.Op Sy.Integer_log2, l

      (* should not happend thanks to well typedness *)
      | ("float"
        | "float32"
        | "float32d"
        | "float64"
        | "float64d"
        | "integer_round"
        | "fixed"
        | "sqrt_real"
        | "abs_int"
        | "abs_real"
        | "real_of_int"
        | "int_floor"
        | "int_ceil"
        | "max_real"
        | "max_int"
        | "min_real"
        | "min_int"
        | "integer_log2"
        | "power_of"), _ ->
        assert false
      | _ -> s, l
    in
    E.mk_term s l ty
  | _ -> E.mk_term s l ty

let empty_cache () =
  cache := MQ.empty
