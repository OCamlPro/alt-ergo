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

(** Print the given counterexample on the given formatter with the
    corresponding format set with Options.get_output_format.
    - functions: the functions of the model;
    - constants: the variables of the model;
    - arrays: (experimental) the arrays of the model.
*)
val output_concrete_model :
  Format.formatter ->
  Expr.Set.t ->
  functions:Profile.V.t Profile.P.t ->
  constants:Profile.V.t Profile.P.t ->
  arrays:Profile.V.t Profile.P.t ->
  unit
