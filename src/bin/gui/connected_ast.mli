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
  ?register:bool -> env -> int -> aform -> Util.axiom_kind -> string ->
  string list -> unit

val readd_trigger : ?register:bool -> env -> int -> string -> bool -> unit
