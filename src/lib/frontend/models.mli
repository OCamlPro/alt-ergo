(******************************************************************************)
(*                                                                            *)
(*     Alt-Ergo: The SMT Solver For Software Verification                     *)
(*     Copyright (C) 2020-2020 --- OCamlPro SAS                               *)
(*                                                                            *)
(*     This file is distributed under the terms of the license indicated      *)
(*     in the file 'License.OCamlPro'. If 'License.OCamlPro' is not           *)
(*     present, please contact us to clarify licensing.                       *)
(*                                                                            *)
(******************************************************************************)

(** {1 Models module} *)

type objective_value =
  | Obj_pinfty
  | Obj_minfty
  | Obj_val of string
  | Obj_unk

type t = {
  propositional : Expr.Set.t;
  constants : Profile.V.t Profile.P.t;
  functions : Profile.V.t Profile.P.t;
  arrays : Profile.V.t Profile.P.t;
  objectives : (Expr.t * objective_value) Util.MI.t;
}

(** Print the given counterexample on the given formatter with the
    corresponding format setted with Options.get_output_format *)
val output_concrete_model :
  Format.formatter ->
  t ->
  unit
