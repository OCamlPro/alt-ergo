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

type t = { delayed : Rel_utils.Delayed.t }

(* Currently we only compute, but in the future we may want to perform the same
   simplifications as in [Bitv.make]. We currently don't, because we don't
   really have a way to share code that uses polynome between the theory and the
   relations without touching the Shostak [module rec].

   Note that if we *do* want to compute here, the check for [X.is_constant] in
   [Rel_utils.update] needs to be removed, which may have (small) performance
   implications. *)
let bv2nat _op bv =
  match Bitv.to_Z_opt bv with
  | Some n -> Some (Shostak.Polynome.create [] (Q.of_bigint n) Tint)
  | None -> None

(* [int2bv] is in the bitvector theory rather than the arithmetic theory because
   we treat the arithmetic as more "primitive" than bit-vectors. *)
let int2bv op p =
  match op, Shostak.Polynome.is_const p with
  | Symbols.Int2BV n, Some q ->
    assert (Z.equal (Q.den q) Z.one);
    let m = Q.to_bigint q in
    Some (Bitv.int2bv_const n m)
  | Int2BV _, None -> None
  | _ -> assert false

let delay1 = Rel_utils.delay1

let dispatch = function
  | Symbols.BV2Nat ->
    Some (delay1 Shostak.Bitv.embed Shostak.Arith.is_mine bv2nat)
  | Int2BV _ ->
    Some (delay1 Shostak.Arith.embed Shostak.Bitv.is_mine int2bv)
  | _ -> None

let empty _ = { delayed = Rel_utils.Delayed.create dispatch }
let assume env uf la =
  let delayed, result = Rel_utils.Delayed.assume env.delayed uf la in
  { delayed }, result
let query _ _ _ = None
let case_split _ _ ~for_model:_ ~to_optimize:_ = Sig_rel.Split []
let add env uf r t =
  let delayed, eqs = Rel_utils.Delayed.add env.delayed uf r t in
  { delayed }, eqs
let new_terms _ = Expr.Set.empty
let instantiate ~do_syntactic_matching:_ _ env _ _ = env, []

let assume_th_elt t th_elt _ =
  match th_elt.Expr.extends with
  | Util.Bitv ->
    failwith "This Theory does not support theories extension"
  | _ -> t
