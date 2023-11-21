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

module X = Shostak.Combine

module Sy = Symbols
module E = Expr


module P = Map.Make
    (struct
      type t = Sy.t * Ty.t list * Ty.t

      let (|||) c1 c2 = if c1 <> 0 then c1 else c2

      let compare (a1, b1, c1)  (a2, b2, c2) =
        let l1_l2 = List.length b1 - List.length b2 in
        let c = l1_l2 ||| (Ty.compare c1 c2) ||| (Sy.compare a1 a2) in
        if c <> 0 then c
        else
          let c = ref 0 in
          try
            List.iter2
              (fun ty1 ty2 ->
                 let d = Ty.compare ty1 ty2 in
                 if d <> 0 then begin c := d; raise Exit end
              ) b1 b2;
            0
          with
          | Exit -> assert (!c <> 0); !c
          | Invalid_argument _ -> assert false
    end)

module V = Set.Make
    (struct
      type t = (E.t * (X.r * string)) list * (X.r * string)
      let compare (l1, (v1,_)) (l2, (v2,_)) =
        let c = X.hash_cmp v1 v2 in
        if c <> 0 then c
        else
          let c = ref 0 in
          try
            List.iter2
              (fun (_,(x,_)) (_,(y,_)) ->
                 let d = X.hash_cmp x y in
                 if d <> 0 then begin c := d; raise Exit end
              ) l1 l2;
            !c
          with
          | Exit -> !c
          | Invalid_argument _ -> List.length l1 - List.length l2
    end)

type key = P.key
type elt = V.t

type t = {
  values : V.t P.t;
  suspicious : bool;
}

let is_suspicious_name hs =
  match Hstring.view hs with
  | "@/" | "@%" | "@*" -> true
  | _ -> false

(* The model generation is known to be imcomplete for FPA and Bitvector
   theories. *)
let is_suspicious_symbol = function
  | Sy.Op (Float | Abs_int | Abs_real | Sqrt_real
          | Sqrt_real_default | Sqrt_real_excess
          | Real_of_int | Int_floor | Int_ceil
          | Max_int | Max_real | Min_int | Min_real
          | Pow | Integer_log2 | Int2BV _ | BV2Nat
          | BVand | BVor | Integer_round) -> true
  | Sy.Name (hs, _, _) when is_suspicious_name hs -> true
  | _ -> false

let add ((sy, _, _) as p) v { values; suspicious } =
  let prof_p = try P.find p values with Not_found -> V.empty in
  let values =
    if V.mem v prof_p then values
    else P.add p (V.add v prof_p) values
  in
  { values; suspicious = suspicious || is_suspicious_symbol sy }

let iter f { values; _ } =
  P.iter (fun ((sy, _, _) as key) value ->
      match sy with
      | Sy.Name (_, _, true) ->
        (* We don't print constants defined by the user. *)
        ()
      | _ -> f key value
    ) values

let[@inline always] is_suspicious { suspicious; _ } = suspicious

let fold f { values; _ } acc = P.fold f values acc

let empty = { values = P.empty; suspicious = false }

let is_empty { values; _ } = P.is_empty values
