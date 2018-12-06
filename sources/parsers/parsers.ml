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
      eprintf
        "Warning: A parser for extension %S is already registered. \
         It will be hidden !@." lang;
    end;
  parsers := (lang, new_parser) :: !parsers

let debug_no_parser_for_extension s =
  if verbose() then
    eprintf
      "error: no parser registered for ext %S. Using default lang ...@." s

let debug_no_parser_for_default_lang s =
  if verbose() then
    eprintf
      "error: no parser registered for the provided default lang %S ?@." s

let get_parser lang_opt =
  let d = Options.default_input_lang () in
  match lang_opt with
  | Some lang ->
    begin
      try List.assoc lang !parsers
      with Not_found ->
        debug_no_parser_for_extension lang;
        try List.assoc d !parsers
        with Not_found ->
          debug_no_parser_for_default_lang d;
          exit 1
    end

  | None ->
    begin
      try List.assoc d !parsers
      with Not_found ->
        debug_no_parser_for_default_lang d;
        exit 1
    end


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
      if verbose () then
        eprintf
          "I'll read the content of '%s' in the given zip@."
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
  if verbose() then fprintf fmt "[input_lang] parsing file %s@." file;
  let cin, lb, opened_cin, ext =
    if Filename.check_suffix file ".zip" then
      let ext = Filename.extension (Filename.chop_extension file) in
      let file_content = extract_zip_file file in
      stdin, Lexing.from_string file_content, false, ext
    else
      let ext = Filename.extension file in
      if Pervasives.(<>) file "" then
        let cin = open_in file in
        cin, Lexing.from_channel cin, true, ext
      else
        stdin, Lexing.from_channel stdin, false, ext
  in
  try
    let ext = if String.equal ext "" then None else Some ext in
    let a = parse_file ?lang:ext lb in
    if opened_cin then close_in cin;
    if parse_only () then exit 0;
    a
  with
  | Errors.Lexical_error (loc, s) ->
    Loc.report err_formatter loc;
    eprintf "lexical error: %s\n@." s;
    if opened_cin then close_in cin;
    exit 1

  | Errors.Syntax_error (loc, s) ->
    Loc.report err_formatter loc;
    eprintf "syntax error when reading token %S\n@." s;
    if opened_cin then close_in cin;
    exit 1

let parse_problem ~filename ~preludes =
  let acc = parse_input_file filename in
  List.fold_left
    (fun acc prelude ->
       let prelude =
         if Sys.file_exists prelude then prelude
         else Config.preludesdir ^ "/" ^ prelude
       in
       List.rev_append (List.rev (parse_input_file prelude)) acc)
    acc (List.rev preludes)
