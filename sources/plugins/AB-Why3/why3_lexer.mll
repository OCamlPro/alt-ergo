(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2017   --   INRIA - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

(******************************************************************************)
(*                                                                            *)
(*     Alt-Ergo: The SMT Solver For Software Verification                     *)
(*     Copyright (C) 2018 --- OCamlPro SAS                                    *)
(*                                                                            *)
(******************************************************************************)

{
  open AltErgoLib
  open AltErgoParsers
  open Why3_parser
  open Lexing

  exception UnterminatedComment
  exception UnterminatedString
  exception IllegalCharacter of char

  let optmap f = function None -> None | Some x -> Some (f x)

  (*let () = Why3_exn_printer.register (fun fmt e -> match e with
    | IllegalCharacter c -> fprintf fmt "illegal character %c" c
    | _ -> raise e)*)

  let keywords = Hashtbl.create 97
  let () =
    List.iter
      (fun (x,y) -> Hashtbl.add keywords x y)
      [
        "as", AS;
        "axiom", AXIOM;
        "clone", CLONE;
        "constant", CONSTANT;
        "else", ELSE;
        "end", END;
        "epsilon", EPSILON;
        "exists", EXISTS;
        "export", EXPORT;
        "false", FALSE;
        "forall", FORALL;
        "function", FUNCTION;
        "goal", GOAL;
        "if", IF;
        "import", IMPORT;
        "in", IN;
        "lemma", LEMMA;
        "let", LET;
        "namespace", NAMESPACE;
        "not", NOT;
        "predicate", PREDICATE;
        "then", THEN;
        "theory", THEORY;
        "true", TRUE;
        "type", TYPE;
        "use", USE;
        "with", WITH;
        (* programs *)
        "ghost", GHOST;
        "invariant", INVARIANT;
        "model", MODEL;
        "val", VAL
      ]

        let update_loc lexbuf file line chars =
    let pos = lexbuf.lex_curr_p in
    let new_file = match file with None -> pos.pos_fname | Some s -> s in
    lexbuf.lex_curr_p <-
      { pos with
          pos_fname = new_file;
          pos_lnum = line;
          pos_bol = pos.pos_cnum - chars;
      }

          let newline lexbuf =
    let pos = lexbuf.lex_curr_p in
    lexbuf.lex_curr_p <-
      { pos with pos_lnum = pos.pos_lnum + 1; pos_bol = pos.pos_cnum }

          let remove_underscores s =
    if String.contains s '_' then begin
      let count =
        let nb = ref 0 in
        String.iter (fun c -> if c = '_' then incr nb) s;
        !nb in
      let t = Bytes.create (String.length s - count) in
      let i = ref 0 in
      String.iter (fun c -> if c <> '_' then (Bytes.set t !i c; incr i)) s;
      Bytes.unsafe_to_string t
      end else s

                   let loc lb = (lexeme_start_p lb, lexeme_end_p lb)

let string_start_loc = ref Loc.dummy
  let string_buf = Buffer.create 1024

  let comment_start_loc = ref Loc.dummy

  let char_for_backslash = function
    | 'n' -> '\n'
    | 't' -> '\t'
    | c -> c
}
let newline = '\n'
let space = [' ' '\t' '\r']
let lalpha = ['a'-'z' '_']
let ualpha = ['A'-'Z']
let alpha = lalpha | ualpha
let digit = ['0'-'9']
let digit_or_us = ['0'-'9' '_']
let alpha_no_us = ['a'-'z' 'A'-'Z']
let suffix = (alpha_no_us | '\''* digit_or_us)* '\''*
let lident = lalpha suffix
let uident = ualpha suffix
let lident_quote = lident ('\'' alpha_no_us suffix)+
let uident_quote = uident ('\'' alpha_no_us suffix)+
let hexadigit = ['0'-'9' 'a'-'f' 'A'-'F']

let op_char_1 = ['=' '<' '>' '~']
let op_char_2 = ['+' '-']
let op_char_3 = ['*' '/' '\\' '%']
let op_char_4 = ['!' '$' '&' '?' '@' '^' '.' ':' '|' '#']
let op_char_34 = op_char_3 | op_char_4
let op_char_234 = op_char_2 | op_char_34
let op_char_1234 = op_char_1 | op_char_234

let op_char_pref = ['!' '?']

rule token = parse
  | "##" space* ("\"" ([^ '\010' '\013' '"' ]* as file) "\"")?
    space* (digit+ as line) space* (digit+ as char) space* "##"
      { update_loc lexbuf file (int_of_string line) (int_of_string char);
        token lexbuf }
  | '\n'
      { newline lexbuf; token lexbuf }
  | space+
      { token lexbuf }
  | '_'
      { UNDERSCORE }
  | lident as id
      { try Hashtbl.find keywords id with Not_found -> LIDENT id }
  | lident_quote as id
      { LIDENT_QUOTE id }
  | uident as id
      { UIDENT id }
  | uident_quote as id
      { UIDENT_QUOTE id }
  | ['0'-'9'] ['0'-'9' '_']* as s
      { INTEGER ((remove_underscores s)) }
(*| '0' ['x' 'X'] (['0'-'9' 'A'-'F' 'a'-'f']['0'-'9' 'A'-'F' 'a'-'f' '_']* as s)
    { INTEGER (Why3_number.int_const_hex (Why3_lexlib.remove_underscores s)) }
| '0' ['o' 'O'] (['0'-'7'] ['0'-'7' '_']* as s)
    { INTEGER (Why3_number.int_const_oct (Why3_lexlib.remove_underscores s)) }
| '0' ['b' 'B'] (['0'-'1'] ['0'-'1' '_']* as s)
    { INTEGER (Why3_number.int_const_bin (Why3_lexlib.remove_underscores s)) }*)
(* | (digit+ as i) ("" as f) ['e' 'E'] (['-' '+']? digit+ as e)
 | (digit+ as i) '.' (digit* as f) (['e' 'E'] (['-' '+']? digit+ as e))?
 | (digit* as i) '.' (digit+ as f) (['e' 'E'] (['-' '+']? digit+ as e))?
    { REAL (Why3_number.real_const_dec i f
        (optmap Why3_lexlib.remove_leading_plus e)) }*)
(*| '0' ['x' 'X'] (hexadigit+ as i) ("" as f) ['p' 'P'] (['-' '+']? digit+ as e)
  | '0' ['x' 'X'] (hexadigit+ as i) '.' (hexadigit* as f)
        (['p' 'P'] (['-' '+']? digit+ as e))?
  | '0' ['x' 'X'] (hexadigit* as i) '.' (hexadigit+ as f)
        (['p' 'P'] (['-' '+']? digit+ as e))?
      { REAL (Why3_number.real_const_hex i f
          (optmap Why3_lexlib.remove_leading_plus e)) }*)
  | "(*)"
      { LEFTPAR_STAR_RIGHTPAR }
  | "(*"
      { comment lexbuf; token lexbuf }
  | "'" (lident as id)
      { QUOTE_LIDENT id }
  | "'" (uident as id)
      { QUOTE_UIDENT id }
  | ","
      { COMMA }
  | "("
      { LEFTPAR }
  | ")"
      { RIGHTPAR }
  | "{"
      { LEFTBRC }
  | "}"
      { RIGHTBRC }
  | ":"
      { COLON }
  | ";"
      { SEMICOLON }
  | "->"
      { ARROW }
  | "<->"
      { LRARROW }
  | "/\\"
      { AND }
  | "\\/"
      { OR }
  | "."
      { DOT }
  | "|"
      { BAR }
  | "<"
      { LT }
  | ">"
      { GT }
  | "<>"
      { LTGT }
  | "="
      { EQUAL }
  | "["
      { LEFTSQ }
  | "]"
      { RIGHTSQ }
  | op_char_pref op_char_4* as s
      { OPPREF s }
  | op_char_1234* op_char_1 op_char_1234* as s
      { OP1 s }
  | op_char_234*  op_char_2 op_char_234*  as s
      { OP2 s }
  | op_char_34*   op_char_3 op_char_34*  as s
      { OP3 s }
  | op_char_4+ as s
      { OP4 s }
  | "\""
      { STRING (string lexbuf) }
  | eof
      { EOF }
  | _ as c
      { raise (IllegalCharacter c) }
and comment = parse
  | "(*)"
      { comment lexbuf }
  | "*)"
      { () }
  | "(*"
      { comment lexbuf; comment lexbuf }
  | newline
      { newline lexbuf; comment lexbuf }
  | eof
      {
        raise (Why3_loc.Why3_located (!comment_start_loc, UnterminatedComment))
      }
  | _
      { comment lexbuf }

and string = parse
  | "\""
      { let s = Buffer.contents string_buf in
        Buffer.clear string_buf;
        s }
  | "\\" (_ as c)
      { if c = '\n' then newline lexbuf;
        Buffer.add_char string_buf (char_for_backslash c); string lexbuf }
  | newline
      { newline lexbuf; Buffer.add_char string_buf '\n'; string lexbuf }
  | eof
      { raise (Why3_loc.Why3_located (!string_start_loc, UnterminatedString)) }
  | _ as c
      { Buffer.add_char string_buf c; string lexbuf }

{
          let comment lexbuf = comment_start_loc := loc lexbuf; comment lexbuf

  let string lexbuf = string_start_loc := loc lexbuf; string lexbuf

  module Parser : Parsers.PARSER_INTERFACE = struct
    let file    = Why3_parser.file_parser     token
    let expr    = Why3_parser.lexpr_parser    token
    let trigger = Why3_parser.trigger_parser  token
  end

  let () = (* register this parser in Input_lang *)
    let p = (module Parser : Parsers.PARSER_INTERFACE) in
    Parsers.register_parser ~lang:".why" p;
    Parsers.register_parser ~lang:".why3" p;

 }
