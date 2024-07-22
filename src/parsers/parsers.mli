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
