(******************************************************************************)
(*                                                                            *)
(*     Alt-Ergo: The SMT Solver For Software Verification                     *)
(*     Copyright (C) 2018-2018 --- OCamlPro SAS                               *)
(*                                                                            *)
(*     This file is distributed under the terms of the license indicated      *)
(*     in the file 'License.OCamlPro'. If 'License.OCamlPro' is not           *)
(*     present, please contact us to clarify licensing.                       *)
(*                                                                            *)
(******************************************************************************)

module Sy = Symbols
module E = Expr

let mk_fp_app s hs l =
  match Hstring.view hs, l with
  | "float", [prec; exp; mode; x] ->
    Sy.Op (Sy.Float (E.int_of_term prec, E.int_of_term exp)), [mode; x]

  | "float32", [_;_;] -> Sy.Op (Sy.Float (24, 149)), l
  | "float32d", [_] ->
    Sy.Op (Sy.Float (24, 149)),
    Fpa_rounding._NearestTiesToEven__rounding_mode :: l

  | "float64", [_;_;] -> Sy.Op (Sy.Float (53, 1074)), l
  | "float64d", [_] ->
    Sy.Op (Sy.Float (53, 1074)),
    Fpa_rounding._NearestTiesToEven__rounding_mode :: l

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

let mk_bv_app s hs l =
  match Hstring.view hs, l with
  | "bvget", [ x; i ] -> Sy.Op (Sy.BVGet (E.int_of_term i)), [x]
  | "bv2nat", [_] -> Sy.Op Sy.BV2Nat, l
  | "nat2bv", [ m; n ] -> Sy.Op (Sy.Nat2BV (E.int_of_term m)), [n]
  | _ -> s, l

let make_adequate_app s l ty =
  match s with
  | Sy.Name (hs, Sy.Other) ->
    let s, l =
      if Options.get_use_fpa ()
      then
        if Options.get_use_bv ()
        then
          let s, l = mk_fp_app s hs l in
          mk_bv_app s hs l
        else mk_fp_app s hs l
      else if Options.get_use_bv ()
      then mk_bv_app s hs l
      else s, l
    in
    E.mk_term s l ty
  | _ -> E.mk_term s l ty
