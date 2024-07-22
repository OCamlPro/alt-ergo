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
(*     The Alt-Ergo theorem prover                                        *)
(*                                                                        *)
(*     Sylvain Conchon, Evelyne Contejean, Francois Bobot                 *)
(*     Mohamed Iguernelala, Stephane Lescuyer, Alain Mebsout              *)
(*                                                                        *)
(*     CNRS - INRIA - Universite Paris Sud                                *)
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

type lit_origin =
  | Subst
  | CS of theory * Numbers.Q.t
  | NCS of theory * Numbers.Q.t
  | Other

(* TODO: use a record to document this type. *)
type case_split = Shostak.Combine.r Xliteral.view * bool * lit_origin

type optimized_split = {
  value : Objective.Value.t;
  case_split : case_split;
}

type 'literal acts = {
  acts_add_decision_lit : 'literal -> unit ;
  acts_add_split : 'literal -> unit ;
  acts_add_objective :
    Objective.Function.t -> Objective.Value.t -> 'literal -> unit ;
}
