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

(** Dynlink wrapper

    A wrapper of the Dynlink module: we use Dynlink except when we want to
    generate a static (native) binary **)

type error
(** Type error, as in {!Dynlink.error} *)

exception Error of error
(** Error exception, as in {!Dynlink.Error} *)

val error_message : error -> string
(** Error messages as strings, as in {!Dynlink.error_message} *)

val loadfile : string -> unit
(** Load a compiled file, as in {!Dynlink.loadfile}. *)

val load : bool -> string -> string -> unit
(** Same as loadfile but try to load plugins dir if loadfile raise an Error
    @raise Errors.Error if the plugin failed to be loaded *)
