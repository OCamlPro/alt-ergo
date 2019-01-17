(******************************************************************************)
(*                                                                            *)
(*     Alt-Ergo: The SMT Solver For Software Verification                     *)
(*     Copyright (C) 2018-2018 --- OCamlPro SAS                               *)
(*                                                                            *)
(*     This file is distributed under the terms of the Apache Software        *)
(*     License version 2.0                                                    *)
(*                                                                            *)
(******************************************************************************)

(** Typed input

    This module defines an abstraction layer over the
    parsing and typechecking of input formulas. The goal is to
    be able to use different parsing and/or typechecking
    engines (e.g. the legacy typechecker, psmt2, or dolmen).
    To do so, an input method actually generates the typed
    representation of the input. *)

exception Method_not_registered of string
(** Exceptions raised when trying to lookup an input method
    that has not been registered. *)

(** This modules defines an input method. Input methods are responsible
    for two things: parsing and typechceking either an input file (possibly
    with some preludes files), or arbitrary terms. This last functionality
    is currently only used in the GUI. *)
module type S = sig

  (** {5 Parsing} *)

  type file
  (** The type of a parsed file (including preludes). *)

  val parse_file : filename:string -> preludes:string list -> file
  (** Parse a file (and some preludes). *)


  (** {5 Typechecking} *)

  type env
  (** The type of local environments used for typechecking. *)

  val type_file : file -> (int Typed.atdecl * env) list * env
  (** Parse and typecheck some input file, together with some prelude files. *)

end

val register : string -> (module S) -> unit
(** Register a new input method. *)

val find : string -> (module S)
(** Find an input method by name.
    @raise Method_not_registered if the name is not registered. *)


