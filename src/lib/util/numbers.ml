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

let select_QNumbers =
  match Config.numbers_lib with
  | "zarith" -> (module ZarithNumbers.Q : NumbersInterface.QSig)
  | "nums" -> (module NumsNumbers.Q : NumbersInterface.QSig)
  | _ -> assert false
(* Choose the library that handle numbers set at configure with
   `./configure --numbers_lib="zarith"|"nums"` *)

[@@@ocaml.warning "-60"]

module MyQNumbers : NumbersInterface.QSig = (val select_QNumbers)

module Z = MyQNumbers.Z

module Q = struct
  include MyQNumbers

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
        if (Stdlib.compare v min_float) < 0 then min_float
        else if (Stdlib.compare v max_float) > 0 then max_float
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
      if MyQNumbers.compare (power cand n) q <= 0 then Some cand else dd

  let accurate_root_excess q n =
    let dd = unaccurate_root_default q n in
    let ee = unaccurate_root_excess  q n in
    match dd, ee with
    | None, _ | _ , None -> ee
    | Some d, Some e ->
      let cand = div (add d e) two in
      if MyQNumbers.compare (power cand n) q >= 0 then Some cand else ee


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

