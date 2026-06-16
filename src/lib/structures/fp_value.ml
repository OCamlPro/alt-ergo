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

type t =
  | Plus_infinity
  | Minus_infinity
  | Plus_zero
  | Minus_zero
  | NaN
  | Finite of { neg : bool; biased_exp : int; significand : Z.t }

let compare v1 v2 =
  Util.compare_algebraic v1 v2
    (function
      | Finite f1, Finite f2 ->
        let c = Bool.compare f1.neg f2.neg in
        if c <> 0 then c else
          let c = Int.compare f1.biased_exp f2.biased_exp in
          if c <> 0 then c else
            Z.compare f1.significand f2.significand
      | _, (Plus_infinity | Minus_infinity | Plus_zero
           | Minus_zero | NaN | Finite _) ->
        assert false)

let pp ppf = function
  | Plus_infinity  -> Fmt.pf ppf "+oo"
  | Minus_infinity -> Fmt.pf ppf "-oo"
  | Plus_zero      -> Fmt.pf ppf "+zero"
  | Minus_zero     -> Fmt.pf ppf "-zero"
  | NaN            -> Fmt.pf ppf "NaN"
  | Finite { neg; biased_exp; significand } ->
    Fmt.pf ppf "fp[%b;%d;%s]" neg biased_exp (Z.to_string significand)

let pp_smtlib eb sb ppf = function
  | Plus_infinity  -> Fmt.pf ppf "(_ +oo %d %d)" eb sb
  | Minus_infinity -> Fmt.pf ppf "(_ -oo %d %d)" eb sb
  | Plus_zero      -> Fmt.pf ppf "(_ +zero %d %d)" eb sb
  | Minus_zero     -> Fmt.pf ppf "(_ -zero %d %d)" eb sb
  | NaN            -> Fmt.pf ppf "(_ NaN %d %d)" eb sb
  | Finite { neg; biased_exp; significand } ->
    let bfmt n = Fmt.str "%%0%db" n in
    let sign_s = if neg then "1" else "0" in
    let exp_s = Z.format (bfmt eb) (Z.of_int biased_exp) in
    let sig_s = Z.format (bfmt (sb - 1)) significand in
    Fmt.pf ppf "(fp #b%s #b%s #b%s)" sign_s exp_s sig_s
