module SmtlibParser = Psmt2Frontend.Smtlib_parser
module SmtlibLexer = Psmt2Frontend.Smtlib_lexer
module SmtlibError = Psmt2Frontend.Smtlib_error

let aux aux_fun token lexbuf =
  try
    let res = aux_fun token lexbuf in
    Parsing.clear_parser ();
    res
  with
  | Parsing.Parse_error
  | (*Basics. | MenhirBasics. |*) SmtlibError.Error _ ->
    (* not fully qualified ! backward incompat. in Menhir !!*)
    let loc = (Lexing.lexeme_start_p lexbuf, Lexing.lexeme_end_p lexbuf) in
    let lex = Lexing.lexeme lexbuf in
    Parsing.clear_parser ();
    raise (Errors.Syntax_error (loc, lex))

let file_parser token lexbuf =
  Translate.file_parser (SmtlibParser.commands token lexbuf)

let lexpr_parser token lexbuf =
  Translate.trigger_parser (SmtlibParser.commands token lexbuf)

let trigger_parser token lexbuf =
  Translate.lexpr_parser (SmtlibParser.commands token lexbuf)

module Parser : Parsers.PARSER_INTERFACE = struct
  let file    = aux file_parser    SmtlibLexer.token
  let expr    = aux lexpr_parser   SmtlibLexer.token
  let trigger = aux trigger_parser SmtlibLexer.token
end

let () =
  (*register this parser in Input_lang: 2 different extensions recognized *)
  let p = (module Parser : Parsers.PARSER_INTERFACE) in
  Parsers.register_parser ~lang:".smt2" p;
  Parsers.register_parser ~lang:".psmt2" p;
