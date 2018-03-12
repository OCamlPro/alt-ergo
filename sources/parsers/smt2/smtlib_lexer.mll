(******************************************************************************)
(*                                                                            *)
(* An SMT-LIB 2 for the Alt-Ergo Theorem Prover                               *)
(*                                                                            *)
(******************************************************************************)

{
open Lexing
open Smtlib_parser
open Smtlib_error

let newline lexbuf =
  let pos = lexbuf.lex_curr_p in
  lexbuf.lex_curr_p <-
    { pos with pos_lnum = pos.pos_lnum + 1; pos_bol = pos.pos_cnum }

let current_pos b =
  lexeme_start_p b,
  lexeme_end_p b

let keyword = Hashtbl.create 50
let () =
  List.iter
    (fun (x,y) -> Hashtbl.add keyword x y)
    [ ":all-statistics", ALLSTATS;
      ":assertion-stack-levels", ASSERTIONSTACKLVL;
      ":authors", AUTHORS;
      ":axioms", AXIOMS;
      ":category",CATEGORY;
      ":definition", DEFINITIO;
      ":diagnostic-output-channel", DIAGNOOUTPUTCHAN;
      ":error-behavior", ERRORBEHAV;
      ":extensions",EXTENSIONS;
      ":funs",FUNS;
      ":funs-description",FUNSDESCRIPT;
      ":global-declarations", GLOBALDECLARATIONS;
      ":interactive-mode", INTERACTIVE;
      ":language",LANGUAGE;
      ":license", LICENSE;
      ":name",NAME;
      ":named",NAMED;
      ":notes",NOTES;
      ":pattern", PATTERN;
      ":print-success",PRINTSUCCESS;
      ":produce-assertions", PRODUCEASSERTIONS;
      ":produce-assignments",PRODUCEASSIGNEMENT;
      ":produce-unsat-assumptions", PRODUCEUNSATASSUMPTIONS;
      ":produce-models",PRODUCEMODELS;
      ":produce-proofs",PRODUCEPROOFS;
      ":produce-unsat-cores",PRODUCEUNSATCORES;
      ":random-seed",RANDOMSEED;
      ":reason-unknown",REASONUNKNOWN;
      ":reproducible-ressource-limit",RESSOURCELIMIT;
      ":regular-output-channel",REGULAROUTPUTCHAN;
      ":smt-lib-version",SMTLIBVERSION;
      ":sorts",SORTS;
      ":sorts-description",SORTSDESCRIPTION;
      ":source",SOURCE;
      ":status",STATUTS;
      ":theories",THEORIES;
      ":values",VALUES;
      ":verbosity",VERBOSITY;
      ":version",VERSION;
    ]
}

rule token = parse
| ['\t' ' ' ]+ { token lexbuf }
| ';'  (_ # '\n')* { token lexbuf }
| '\n' { new_line lexbuf; token lexbuf }
| "_" { UNDERSCORE }
| "(" { LP }
| ")" { RP }
| "par" { PAR }
| "as" { AS }
| "let" { LET }
| "forall" { FORALL }
| "exists" { EXISTS }
| "match" { MATCH }
| "!" { EXCLIMATIONPT }
| "set-logic" { SETLOGIC }
| "set-option" { SETOPTION }
| "set-info" { SETINFO }
| "declare-sort" { DECLARESORT }
| "define-sort" { DEFINESORT }
| "declare-const" { DECLARECONST }
| "declare-fun" { DECLAREFUN }
| "define-fun" { DEFINEFUN }
| "define-fun-rec" { DEFINEFUNREC }
| "define-funs-rec" { DEFINEFUNSREC }
| "declare-datatypes" {DECLAREDATATYPES}
| "declare-datatype" {DECLAREDATATYPE}
| "push" { PUSH }
| "pop" { POP }
| "echo" { ECHO }
| "assert" { ASSERT }
| "check-sat" { CHECKSAT }
| "check-sat-assuming" { CHECKSATASSUMING }
| "get-assertions" { GETASSERT }
| "get-proof" { GETPROOF }
| "get-unsat-core" { GETUNSATCORE }
| "get-value" { GETVALUE }
| "get-assignment" { GETASSIGN }
| "get-unsat-assumptions" { GETUNSATASSUMPTIONS }
| "get-option" { GETOPTION }
| "get-info" { GETINFO }
| "get-model" { GETMODEL }
| "reset" { RESET }
| "reset-assertions" { RESETASSERTIONS }
| "exit" { EXIT }
|  '#' 'x' ['0'-'9' 'A'-'F' 'a'-'f']+  as str { HEXADECIMAL(str) }
|  '#' 'b' ['0'-'1']+  as str { BINARY(str) }
|  '|' (['!'-'~' '\128'-'\255' ' ' '\n' '\t' '\r'] # ['|'])* '|'
    as str { ASCIIWOR(str) }
|  ':' ['a'-'z' 'A'-'Z' '0'-'9' '+' '-' '/' '*' '=' '%' '?' '!' '.' '$'
	   '_' '~' '&' '^' '<' '>' '@']+
	as str { try Hashtbl.find keyword str
	  with Not_found ->
	    error (Lexical_error ("unknown Keyword : " ^ lexeme lexbuf))
	      (current_pos lexbuf) }
|  ['a'-'z' 'A'-'Z' '+' '-' '/' '*' '=''%' '?' '!' '.' '$' '_' '~' '&'
       '^' '<' '>' '@'] ['a'-'z' 'A'-'Z' '0'-'9' '+' '-' '/' '*' '=''%'
			    '?' '!' '.' '$' '_' '~' '&' '^' '<' '>' '@']*
    as str { SYMBOL(str) }
| '"' { comment "" lexbuf }
|  ( '0' | ['1'-'9'] ['0'-'9']* ) '.' ['0'-'9']+
		as str { DECIMAL(str) }
|  ( '0' | ['1'-'9'] ['0'-'9']* )
	    as str { NUMERAL(str) }
| eof { EOF }
| _ {error (Lexical_error ("empty token " ^ lexeme lexbuf))
	      (current_pos lexbuf) }

and comment acc = parse
| "\"\"" { comment (Printf.sprintf "%s\"" acc) lexbuf }
| '"' { STRINGLIT(acc)}
| _ as c { comment (Printf.sprintf "%s%c" acc c) lexbuf }


{
  module Parser : Parsers.PARSER_INTERFACE = struct
    let file    = Smtlib_parser.file_parser    token
    let expr    = Smtlib_parser.lexpr_parser   token
    let trigger = Smtlib_parser.trigger_parser token
  end

  let () =
    (*register this parser in Input_lang: 2 different extensions recognized *)
    let p = (module Parser : Parsers.PARSER_INTERFACE) in
    Parsers.register_parser ~lang:".smt2" p;
    Parsers.register_parser ~lang:".psmt2" p;
}
