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

(** {1 Models module} *)

type objective_value =
  | Obj_pinfty
  | Obj_minfty
  | Obj_val of string
  | Obj_unk

type t = {
  propositional : Expr.Set.t;
  constants : ModelMap.t;
  functions : ModelMap.t;
  arrays : ModelMap.t;
  objectives: (Expr.t * objective_value) Util.MI.t;
  terms_values : (Shostak.Combine.r * string) Expr.Map.t
  (** A map from terms to their values in the model (as a
      representative of type X.r and as a string. *)
}

val output_concrete_model : t Fmt.t
(** [output_concrete_model ppf mdl] prints the model [mdl] on
    the formatter [ppf]. *)
