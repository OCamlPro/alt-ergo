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

open AltErgoLib
open Annoted_ast


val prune : ?register:bool -> env -> 'a annoted -> unit

val incorrect_prune : ?register:bool -> env -> 'a annoted -> unit

val unprune : ?register:bool -> env -> 'a annoted -> unit

val toggle_prune : env -> 'a annoted -> unit

val connect : env -> unit

val clear_used_lemmas_tags : env -> unit

val show_used_lemmas : env -> Explanation.t -> unit

val prune_unused : env -> unit

val add_instance :
  ?register:bool -> env -> int -> aform -> Parsed.axiom_kind -> string ->
  string list -> unit

val readd_trigger : ?register:bool -> env -> int -> string -> bool -> unit
