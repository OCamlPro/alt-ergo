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

(** Typed input

    This module defines an abstraction layer over the
    parsing and typechecking of input formulas. The goal is to
    be able to use different parsing and/or typechecking
    engines (e.g. the legacy typechecker, psmt2, or dolmen).
    To do so, an input method actually generates the typed
    representation of the input. *)

(** {3 Input method} *)

exception Method_not_registered of string
(** Exceptions raised when trying to lookup an input method
    that has not been registered. *)

(** This modules defines an input method. Input methods are responsible
    for two things: parsing and typechceking either an input file (possibly
    with some preludes files), or arbitrary terms. This last functionality
    is currently only used in the GUI. *)
module type S = sig

  (** {5 Parsing} *)

  type parsed
  (** The type of a parsed statement. *)

  val parse_file : content:string -> format:string option -> parsed Seq.t
  (** Parse a file as a string with the given format or the input_format set *)

  val parse_files : filename:string -> preludes:string list -> parsed Seq.t
  (** Parse a file (and some preludes). *)

  type env
  (** Global typing environment *)

  val empty_env : env
  (** The empty/initial environment *)

  val type_parsed :
    env -> env Stack.t -> parsed -> int Typed.atdecl list * env
    (** Parse and typecheck some input file,
        together with some prelude files. *)

end

val register : string -> (module S) -> unit
(** Register a new input method. *)

val find : string -> (module S)
(** Find an input method by name.
    @raise Method_not_registered if the name is not registered. *)
