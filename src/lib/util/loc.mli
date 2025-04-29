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

(** Position in input files

    This module defines a notion of location in files.
    Note: this only specifies a position in an arbitrary file,
          it does not contain information about the file itself.
*)

type t = Lexing.position * Lexing.position
(** The type of locations, a location is made up of two position in the file,
    respectively corresponding to the beginning and end of the location. *)

val from_dolmen_loc : Dolmen.Std.Loc.loc -> t

val dummy : t
(** A dummy location. *)

val report : Format.formatter -> t -> unit
(** Report a location on the given formatter, using standard
    human-redable location reporting. *)
