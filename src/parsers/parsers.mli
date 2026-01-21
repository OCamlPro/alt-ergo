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

open AltErgoLib

module type PARSER_INTERFACE = sig
  val file : Lexing.lexbuf -> Parsed.file
  val expr : Lexing.lexbuf -> Parsed.lexpr
  val trigger : Lexing.lexbuf -> Parsed.lexpr list * bool
end
(** The interface that should be provided by every lexer/parser of an
    input language *)

val register_parser : lang:string -> (module PARSER_INTERFACE) -> unit
(** Registers a new 'parser' for the given extension/language *)

val parse_file : ?lang:string -> Lexing.lexbuf -> Parsed.file
(** Parses the given file (lexbuf) using the appropriate 'parser'
    depending on the given language (set from extension) or
    the format set with the --input option.
    If no output format is set with the --output option, we set it depending
    on the extension / input format. by default if an input format is set
    results will be printed according this input format.
    @raise Errors.Parser_error *)

val parse_expr : ?lang:string -> Lexing.lexbuf -> Parsed.lexpr
(** Parses the given expression (lexbuf) using the appropriate 'parser'
    depending on the given language. If no language is given, the
    default one is used.
    @raise Errors.Parser_error *)

val parse_trigger : ?lang:string -> Lexing.lexbuf -> Parsed.lexpr list * bool
(** Parses the given trigger (lexbuf) using the appropriate 'parser'
    depending on the given language. If no language is given, the
    default one is used.
    @raise Errors.Parser_error *)

val parse_problem : filename:string -> preludes:string list -> Parsed.file
(** Parses the given input file and eventual preludes. Parsers are
    chosen depending on the extension of different files.
    @raise Errors.Error
    @raise Parsing.Parse_Error *)

val parse_problem_as_string :
  content:string -> format:string option -> Parsed.file
(** Parses the given input file as a string.
    Parser is chosen depending on the given format or the input_format set.
    @raise Errors.Error
    @raise Parsing.Parse_Error *)
