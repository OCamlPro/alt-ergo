(*********************************************************************************)
(*                                                                               *)
(*     Alt-Ergo: The SMT Solver For Software Verification                        *)
(*     Copyright (C) --- OCamlPro SAS                                            *)
(*                                                                               *)
(*     This software is governed by the CeCILL  license under French law and     *)
(*     abiding by the rules of distribution of free software.  You can  use,     *)
(*     modify and/ or redistribute the software under the terms of the CeCILL    *)
(*     license as circulated by CEA, CNRS and INRIA at the following URL         *)
(*     "http://www.cecill.info".                                                 *)
(*                                                                               *)
(*     As a counterpart to the access to the source code and  rights to copy,    *)
(*     modify and redistribute granted by the license, users are provided only   *)
(*     with a limited warranty  and the software's author,  the holder of the    *)
(*     economic rights,  and the successive licensors  have only  limited        *)
(*     liability.                                                                *)
(*                                                                               *)
(*     In this respect, the user's attention is drawn to the risks associated    *)
(*     with loading,  using,  modifying and/or developing or reproducing the     *)
(*     software by the user in light of its specific status of free software,    *)
(*     that may mean  that it is complicated to manipulate,  and  that  also     *)
(*     therefore means  that it is reserved for developers  and  experienced     *)
(*     professionals having in-depth computer knowledge. Users are therefore     *)
(*     encouraged to load and test the software's suitability as regards their   *)
(*     requirements in conditions enabling the security of their systems and/or  *)
(*     data to be ensured and,  more generally, to use and operate it in the     *)
(*     same conditions as regards security.                                      *)
(*                                                                               *)
(*     The fact that you are presently reading this means that you have had      *)
(*     knowledge of the CeCILL license and that you accept its terms.            *)
(*                                                                               *)
(*     ------------------------------------------------------------------------  *)
(*                                                                               *)
(*     This is a free release of Alt-Ergo under the terms of CeCILL license.     *)
(*     The latest releases of Alt-Ergo are distributed under the terms of        *)
(*     OCamlPro Non-Commercial Purpose License, version 1.                       *)
(*                                                                               *)
(*     As an exception, Alt-Ergo Club members at the Gold level can              *)
(*     use this file under the terms of the Apache Software License              *)
(*     version 2.0.                                                              *)
(*                                                                               *)
(*     ------------------------------------------------------------------------  *)
(*                                                                               *)
(*     The Alt-Ergo theorem prover                                               *)
(*                                                                               *)
(*     Sylvain Conchon, Evelyne Contejean, Francois Bobot                        *)
(*     Mohamed Iguernelala, Stephane Lescuyer, Alain Mebsout                     *)
(*                                                                               *)
(*     CNRS - INRIA - Universite Paris Sud                                       *)
(*                                                                               *)
(*     ------------------------------------------------------------------------  *)
(*                                                                               *)
(*     More details can be found in the directory licenses/                      *)
(*                                                                               *)
(*********************************************************************************)

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


