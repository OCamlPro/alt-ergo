(******************************************************************************)
(*                                                                            *)
(*     Alt-Ergo: The SMT Solver For Software Verification                     *)
(*     Copyright (C) 2013-2018 --- OCamlPro SAS                               *)
(*                                                                            *)
(*     This file is distributed under the terms of the license indicated      *)
(*     in the file 'License.OCamlPro'. If 'License.OCamlPro' is not           *)
(*     present, please contact us to clarify licensing.                       *)
(*                                                                            *)
(******************************************************************************)

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

