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

(* To get rid of warnings produced by ppx_deriving. *)
[@@@warning "-32"]

(* The type of modules, followed by the list of every element. *)
type t =
  | M_None
  | M_Combine
  | M_Typing
  | M_Sat
  | M_Match
  | M_CC
  | M_UF
  | M_Arith
  | M_Arrays
  | M_Sum
  | M_Records
  | M_Adt
  | M_Bitv
  | M_AC
  | M_Expr
  | M_Triggers
  | M_Simplex
  | M_Ite
[@@deriving enum]

let all =
  let l = [
    M_None;
    M_Combine;
    M_Typing;
    M_Sat;
    M_Match;
    M_CC;
    M_UF;
    M_Arith;
    M_Arrays;
    M_Sum;
    M_Records;
    M_Adt;
    M_Bitv;
    M_AC;
    M_Expr;
    M_Triggers;
    M_Simplex;
    M_Ite
  ]
  in
  assert ((List.length l) = max + 1);
  l

let show k =
  match k with
  | M_None     -> "None"
  | M_Combine  -> "Combine"
  | M_Typing   -> "Typing"
  | M_Sat      -> "Sat"
  | M_Match    -> "Match"
  | M_CC       -> "CC"
  | M_UF       -> "UF"
  | M_Arith    -> "Arith"
  | M_Arrays   -> "Arrays"
  | M_Sum      -> "Sum"
  | M_Records  -> "Records"
  | M_Adt      -> "Adt"
  | M_Bitv     -> "Bitv"
  | M_AC       -> "AC"
  | M_Expr     -> "Expr"
  | M_Triggers -> "Triggers"
  | M_Simplex  -> "Simplex"
  | M_Ite      -> "Ite"
