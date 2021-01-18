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

type answer = (Explanation.t * Expr.Set.t list) option


type theory =
  | Th_arith
  | Th_sum
  | Th_adt
  | Th_arrays
  | Th_UF

type lit_origin =
  | Subst
  | CS of theory * Numbers.Q.t
  | NCS of theory * Numbers.Q.t
  | Other

type split_info = Shostak.Combine.r Xliteral.view * bool * lit_origin

type optimized_split_value =
  | Minfinity
  | Value of split_info
  | Pinfinity
  | Unknown

type optimized_split =
  { r : Shostak.Combine.r;
    e : Expr.t;
    value : optimized_split_value;
    is_max : bool; (* for linear arithmetic: is_max <-> (opt = maximize) *)
    order : int (* ordering assigned by the user for this variable *)
  }
