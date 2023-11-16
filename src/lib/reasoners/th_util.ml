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
  | Th_bitv
  | Th_UF
[@@deriving show]

type limit_kind =
  | Above
  | Below

type 'a optimized_split_value =
  | Minfinity
  | Pinfinity
  | Value of 'a
  | Limit of limit_kind * 'a
  | Unknown

type lit_origin =
  | Subst
  | CS of theory * Numbers.Q.t
  | NCS of theory * Numbers.Q.t
  | Other

(* TODO: use a record to document this type. *)
type case_split = Shostak.Combine.r Xliteral.view * bool * lit_origin

type optimized_split = {
  r : Shostak.Combine.r;
  e : Expr.t;
  value : Expr.t optimized_split_value;
  case_split : case_split option;
  is_max : bool;
  (** For linear arithmetic: is_max <-> (opt = maximize). *)

  order : int
  (** Ordering assigned by the user for this variable. *)
}
