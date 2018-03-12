open Options
open Parsed_interface

(* let file_parser = assert false
 * let lexpr_parser = assert false
 * let trigger_parser = assert false
 * 
 * let aux aux_fun token lexbuf =
 *   try
 *     let res = aux_fun token lexbuf in
 *     Parsing.clear_parser ();
 *     res
 *   with
 *   | Parsing.Parse_error
 *   | (\*Basics. | MenhirBasics.*\)(\* Error *\) _ ->
 *     (\* not fully qualified ! backward incompat. in Menhir !!*\)
 *     let loc = (Lexing.lexeme_start_p lexbuf, Lexing.lexeme_end_p lexbuf) in
 *     let lex = Lexing.lexeme lexbuf in
 *     Parsing.clear_parser ();
 *     raise (Errors.Syntax_error (loc, lex))
 * 
 * let file_parser token lexbuf = aux file_parser token lexbuf
 * let lexpr_parser token lexbuf = aux lexpr_parser token lexbuf
 * let trigger_parser token lexbuf = aux trigger_parser token lexbuf *)


module Parser : Parsers.PARSER_INTERFACE = struct
  let file    = (* file_parser    parse_token *) assert false
  let expr    = (* lexpr_parser   parse_token *) assert false
  let trigger = (* trigger_parser parse_token *) assert false
end

let () =
  (*register this parser in Input_lang: 3 different extensions recognized *)
  let p = (module Parser : Parsers.PARSER_INTERFACE) in
  Parsers.register_parser ~lang:".smt2" p;
  Parsers.register_parser ~lang:".psmt2" p;
