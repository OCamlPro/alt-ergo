(******************************************************************************)
(*                                                                            *)
(*     The Alt-Ergo theorem prover                                            *)
(*     Copyright (C) 2006-2013                                                *)
(*                                                                            *)
(*     Sylvain Conchon                                                        *)
(*     Evelyne Contejean                                                      *)
(*                                                                            *)
(*     Francois Bobot                                                         *)
(*     Mohamed Iguernelala                                                    *)
(*     Stephane Lescuyer                                                      *)
(*     Alain Mebsout                                                          *)
(*                                                                            *)
(*     CNRS - INRIA - Universite Paris Sud                                    *)
(*                                                                            *)
(*     This file is distributed under the terms of the Apache Software        *)
(*     License version 2.0                                                    *)
(*                                                                            *)
(*  ------------------------------------------------------------------------  *)
(*                                                                            *)
(*     Alt-Ergo: The SMT Solver For Software Verification                     *)
(*     Copyright (C) 2013-2018 --- OCamlPro SAS                               *)
(*                                                                            *)
(*     This file is distributed under the terms of the Apache Software        *)
(*     License version 2.0                                                    *)
(*                                                                            *)
(******************************************************************************)

open AltErgoLib
open Options
open Errors
open Format

module type PARSER_INTERFACE = sig
  val file : Lexing.lexbuf -> Parsed.file
  val expr : Lexing.lexbuf -> Parsed.lexpr
  val trigger : Lexing.lexbuf -> Parsed.lexpr list * bool
end

let parsers = ref ([] : (string * (module PARSER_INTERFACE)) list)

let register_parser ~lang new_parser =
  if List.mem_assoc lang !parsers then
    begin
      Printer.print_wrn
        "A parser for extension %S is already registered. \
         It will be hidden !" lang;
    end;
  parsers := (lang, new_parser) :: !parsers

let find_parser ext_opt format =
  try List.assoc ext_opt !parsers
  with Not_found ->
    if String.equal ext_opt ".why" then begin
      Printer.print_wrn
        "please use the AB-Why3 plugin for file in Why3 format. \
         .why and .mlw extensions are depreciated and used for Why3 files. \
         Continue with native Alt-Ergo parsers!";
      try List.assoc ".ae" !parsers
      with Not_found ->
        error (Parser_error ("Error: no parser registered for the provided \
                              input format %S ?@."^format))
    end else
      error (Parser_error ("Error: no parser registered for the provided \
                            input format %S ?@."^format))

let set_output_format fmt =
  if Options.get_infer_output_format () then
    match fmt with
    | Options.Unknown s ->
      Printer.print_wrn
        "The output format %s is not supported" s
    | fmt -> Options.set_output_format fmt

let get_input_parser fmt =
  set_output_format fmt;
  match fmt with
  | Options.Native -> find_parser ".ae" "native"
  | Options.Smtlib2 -> find_parser ".smt2" "smtlib2"
  | Options.Why3 -> find_parser ".why" "why3"
  | Options.Unknown s -> find_parser s s

let get_parser ext_opt =
  if Options.get_infer_input_format () then
    match ext_opt with
    | Some ext ->
      get_input_parser (Options.match_extension ext)
    | None ->
      error
        (Parser_error "Error: no extension found, can't infer input format@.")
  else
    get_input_parser (Options.get_input_format ())

let parse_file ?lang lexbuf =
  let module Parser = (val get_parser lang : PARSER_INTERFACE) in
  Parser.file lexbuf

let parse_expr ?lang lexbuf =
  let module Parser = (val get_parser lang : PARSER_INTERFACE) in
  Parser.expr lexbuf

let parse_trigger ?lang lexbuf =
  let module Parser = (val get_parser lang : PARSER_INTERFACE) in
  Parser.trigger lexbuf

(* pre-condition: f is of the form f'.zip *)
let extract_zip_file f =
  let cin = MyZip.open_in f in
  try
    match MyZip.entries cin with
    | [e] when not (MyZip.is_directory e) ->
      if get_verbose () then
        Printer.print_dbg
          ~module_name:"Parsers" ~function_name:"extract_zip_file"
          "I'll read the content of '%s' in the given zip"
          (MyZip.filename e);
      let content = MyZip.read_entry cin e in
      MyZip.close_in cin;
      content
    | _ ->
      MyZip.close_in cin;
      raise (Arg.Bad
               (sprintf "%s '%s' %s@?"
                  "The zipped file" f
                  "should contain exactly one file."))
  with e ->
    MyZip.close_in cin;
    raise e

let parse_input_file file =
  if get_verbose () then
    Printer.print_dbg
      ~module_name:"Parsers" ~function_name:"parse_input_file"
      "parsing file \"%s\"" file;
  let cin, lb, opened_cin, ext =
    if Filename.check_suffix file ".zip" then
      let ext = Filename.extension (Filename.chop_extension file) in
      let file_content = extract_zip_file file in
      stdin, Lexing.from_string file_content, false, ext
    else
      let ext = Filename.extension file in
      if not (String.equal file "") then
        let cin = open_in file in
        cin, Lexing.from_channel cin, true, ext
      else
        stdin, Lexing.from_channel stdin, false, ext
  in
  try
    let ext = if String.equal ext "" then None else Some ext in
    let a = parse_file ?lang:ext lb in
    if opened_cin then close_in cin;
    a
  with
  | Errors.Error e ->
    if opened_cin then close_in cin;
    raise (Error e)

  | Parsing.Parse_error as e ->
    if opened_cin then close_in cin;
    raise e

let parse_problem ~filename ~preludes =
  Parsers_loader.load ();
  let acc = parse_input_file filename in
  List.fold_left
    (fun acc prelude ->
       let prelude =
         if Sys.file_exists prelude then prelude
         else Config.preludesdir ^ "/" ^ prelude
       in
       List.rev_append (List.rev (parse_input_file prelude)) acc)
    acc (List.rev preludes)
