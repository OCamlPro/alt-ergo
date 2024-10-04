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

val main : unit -> unit
(** Main function solve the input problem. The processed source is given
    by the file located at [Options.get_file ()]. *)

val process_source :
  ?selector_inst:(AltErgoLib.Expr.t -> bool) ->
  print_status:(AltErgoLib.Frontend.status -> int -> unit) ->
  Dolmen_loop.State.source ->
  unit
(** [process_source ?selector_inst ~print_status src] processes the
    input source [src] and call [print_status] on each answers.
    The hook [selector_inst] allows to track generated instantiations. *)
