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

type answer = (Explanation.t * Expr.Set.t list) option


type theory =
  | Th_arith
  | Th_sum
  | Th_adt
  | Th_arrays
  | Th_UF

type 'a optimized_split_value =
  | Minfinity
  | Value of 'a
  | Pinfinity
  | Unknown

type optimization =
  { opt_ord : int; opt_val : Expr.t optimized_split_value }

type lit_origin =
  | Subst
  | CS of optimization option * theory * Numbers.Q.t
  | NCS of theory * Numbers.Q.t
  | Other

type split_info = Shostak.Combine.r Xliteral.view * bool * lit_origin

type optimized_split =
  { r : Shostak.Combine.r;
    e : Expr.t;
    value : split_info optimized_split_value;
    is_max : bool; (* for linear arithmetic: is_max <-> (opt = maximize) *)
    order : int (* ordering assigned by the user for this variable *)
  }
