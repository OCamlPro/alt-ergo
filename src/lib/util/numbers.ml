(******************************************************************************)
(*                                                                            *)
(*  Alt-Ergo: The SMT Solver For Software Verification                        *)
(*  Copyright (C) --- OCamlPro SAS                                            *)
(*                                                                            *)
(*  This software is governed by the CeCILL  license under French law and     *)
(*  abiding by the rules of distribution of free software.  You can  use,     *)
(*  modify and/ or redistribute the software under the terms of the CeCILL    *)
(*  license as circulated by CEA, CNRS and INRIA at the following URL         *)
(*  "http://www.cecill.info".                                                 *)
(*                                                                            *)
(*  As a counterpart to the access to the source code and  rights to copy,    *)
(*  modify and redistribute granted by the license, users are provided only   *)
(*  with a limited warranty  and the software's author,  the holder of the    *)
(*  economic rights,  and the successive licensors  have only  limited        *)
(*  liability.                                                                *)
(*                                                                            *)
(*  In this respect, the user's attention is drawn to the risks associated    *)
(*  with loading,  using,  modifying and/or developing or reproducing the     *)
(*  software by the user in light of its specific status of free software,    *)
(*  that may mean  that it is complicated to manipulate,  and  that  also     *)
(*  therefore means  that it is reserved for developers  and  experienced     *)
(*  professionals having in-depth computer knowledge. Users are therefore     *)
(*  encouraged to load and test the software's suitability as regards their   *)
(*  requirements in conditions enabling the security of their systems and/or  *)
(*  data to be ensured and,  more generally, to use and operate it in the     *)
(*  same conditions as regards security.                                      *)
(*                                                                            *)
(*  The fact that you are presently reading this means that you have had      *)
(*  knowledge of the CeCILL license and that you accept its terms.            *)
(*                                                                            *)
(*  ------------------------------------------------------------------------  *)
(*                                                                            *)
(*  This is a free release of Alt-Ergo under the terms of CeCILL license.     *)
(*  The latest releases of Alt-Ergo are distributed under the terms of        *)
(*  OCamlPro Non-Commercial Purpose License, version 1.                       *)
(*                                                                            *)
(*  ------------------------------------------------------------------------  *)
(*                                                                            *)
(*  The Alt-Ergo theorem prover                                               *)
(*                                                                            *)
(*  Sylvain Conchon, Evelyne Contejean, Francois Bobot                        *)
(*  Mohamed Iguernelala, Stephane Lescuyer, Alain Mebsout                     *)
(*                                                                            *)
(*  CNRS - INRIA - Universite Paris Sud                                       *)
(*                                                                            *)
(*  ------------------------------------------------------------------------  *)
(*                                                                            *)
(*  More details can be found in the directory licenses/                      *)
(*                                                                            *)
(******************************************************************************)

let select_QNumbers =
  match Config.numbers_lib with
  | Zarith -> (module ZarithNumbers.Q : NumbersInterface.QSig)
  | Nums -> (module NumsNumbers.Q : NumbersInterface.QSig)
(* Choose the library that handle numbers set at configure with
   `./configure --numbers_lib="zarith"|"nums"` *)

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

