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
(*     Copyright (C) 2013-2017 --- OCamlPro SAS                               *)
(*                                                                            *)
(*     This file is distributed under the terms of the Apache Software        *)
(*     License version 2.0                                                    *)
(*                                                                            *)
(******************************************************************************)

open Parsed
open Typed


type th_elt =
  {
    th_name : string;
    th_form : Formula.t;
    extends : Typed.theories_extensions;
    axiom_kind : axiom_kind;
  }

(* Sat entry *)

type sat_decl_aux =
  | Assume of string * Formula.t * bool
  | PredDef of Formula.t * string (*name of the predicate*)
  | RwtDef of (Term.t rwt_rule) list
  | Query of string *  Formula.t * goal_sort
  | ThAssume of th_elt

type sat_tdecl = {
  st_loc : Loc.t;
  st_decl : sat_decl_aux
}
