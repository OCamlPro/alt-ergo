(******************************************************************************)
(*                                                                            *)
(*  Alt-Ergo: The SMT Solver For Software Verification                        *)
(*  Copyright (C) --- OCamlPro SAS                                            *)
(*                                                                            *)
(*  This software is governed by the CeCILL  license under French law and     *)
(*  abiding by the rules of distribution of free software.  You can  use,     *)
(*  modify and/ or redistribute the software under the terms of the CeCILL    *)
(*  license as circulated by CEA, CNRS and INRIA at the following URL         *)
(*  "http://www.cecill.info".                                                 *)
(*                                                                            *)
(*  As a counterpart to the access to the source code and  rights to copy,    *)
(*  modify and redistribute granted by the license, users are provided only   *)
(*  with a limited warranty  and the software's author,  the holder of the    *)
(*  economic rights,  and the successive licensors  have only  limited        *)
(*  liability.                                                                *)
(*                                                                            *)
(*  In this respect, the user's attention is drawn to the risks associated    *)
(*  with loading,  using,  modifying and/or developing or reproducing the     *)
(*  software by the user in light of its specific status of free software,    *)
(*  that may mean  that it is complicated to manipulate,  and  that  also     *)
(*  therefore means  that it is reserved for developers  and  experienced     *)
(*  professionals having in-depth computer knowledge. Users are therefore     *)
(*  encouraged to load and test the software's suitability as regards their   *)
(*  requirements in conditions enabling the security of their systems and/or  *)
(*  data to be ensured and,  more generally, to use and operate it in the     *)
(*  same conditions as regards security.                                      *)
(*                                                                            *)
(*  The fact that you are presently reading this means that you have had      *)
(*  knowledge of the CeCILL license and that you accept its terms.            *)
(*                                                                            *)
(*  ------------------------------------------------------------------------  *)
(*                                                                            *)
(*  This is a free release of Alt-Ergo under the terms of CeCILL license.     *)
(*  The latest releases of Alt-Ergo are distributed under the terms of        *)
(*  OCamlPro Non-Commercial Purpose License, version 1.                       *)
(*                                                                            *)
(*  ------------------------------------------------------------------------  *)
(*                                                                            *)
(*  The Alt-Ergo theorem prover                                               *)
(*                                                                            *)
(*  Sylvain Conchon, Evelyne Contejean, Francois Bobot                        *)
(*  Mohamed Iguernelala, Stephane Lescuyer, Alain Mebsout                     *)
(*                                                                            *)
(*  CNRS - INRIA - Universite Paris Sud                                       *)
(*                                                                            *)
(*  ------------------------------------------------------------------------  *)
(*                                                                            *)
(*  More details can be found in the directory licenses/                      *)
(*                                                                            *)
(******************************************************************************)

{
  [@@@ocaml.warning "-33"]
  open AltErgoLib
  open Options

  open Lexing
  open Native_parser

  let assoc_keyword =
    let tbl : (string, Native_parser.token) Hashtbl.t = Hashtbl.create 256 in
    let kw_list =
      [
        "ac"         , AC;
        "and"        , AND;
        "axiom"      , AXIOM;
        "bitv"       , BITV;
        "bool"       , BOOL;
        "case_split" , CASESPLIT;
        "check"      , CHECK;
        "cut"        , CUT;
        "distinct"   , DISTINCT;
        "else"       , ELSE;
        "end"        , END;
        "exists"     , EXISTS;
        "extends"    , EXTENDS;
        "false"      , FALSE;
        "forall"     , FORALL;
        "function"   , FUNC;
        "goal"       , GOAL;
        "if"         , IF;
        "in"         , IN;
        "int"        , INT;
        "let"        , LET;
        "logic"      , LOGIC;
        "not"        , NOT;
        "or"         , OR;
        "xor"         , XOR;
        "predicate"  , PRED;
        "prop"       , PROP;
        "real"       , REAL;
        "rewriting"  , REWRITING;
        "then"       , THEN;
        "theory"     , THEORY;
        "true"       , TRUE;
        "type"       , TYPE;
        "unit"       , UNIT;
        "void"       , VOID;
        "match"      , MATCH;
        "with"       , WITH;
        "of"         , OF;
      ]
    in
    List.iter (fun (s, kw) -> Hashtbl.add tbl s kw) kw_list;
    fun tok -> Hashtbl.find tbl tok

  let mk_new_line lexbuf =
    let p = lexbuf.lex_curr_p in
    let p = { p with pos_lnum = p.pos_lnum + 1; pos_bol = p.pos_cnum } in
    lexbuf.lex_curr_p <- p

  let escaped_char = function
    | 'n' -> '\n'
    | 'r' -> '\r'
    | 't' -> '\t'
    | c -> c

  let n_zero = Num.Int 0
  let n_ten = Num.Int 10
  let n_16 = Num.Int 16

  let decimal_number s =
    let r = ref n_zero in
    for i=0 to String.length s - 1 do
      r := Num.add_num (Num.mult_num n_ten !r)
          (Num.num_of_int (Char.code s.[i] - Char.code '0'))
    done;
    !r

  let hexa_number s =
    let r = ref n_zero in
    for i=0 to String.length s - 1 do
      let c = s.[i] in
      let v =
        match c with
        | '0'..'9' -> Char.code c - Char.code '0'
        | 'a'..'f' -> Char.code c - Char.code 'a' + 10
        | 'A'..'F' -> Char.code c - Char.code 'A' + 10
        | _ -> assert false
      in
      r := Num.add_num (Num.mult_num n_16 !r) (Num.num_of_int v)
    done;
    !r

}

let alphabet = ['a'-'z' 'A'-'Z']
let digit = ['0'-'9']
let hexadecimal = digit | ['a'-'f''A'-'F']
let identifier = (alphabet | '_') (alphabet | '_' | digit | '?' | '\'')*

rule parse_token = parse
  | '\n'                     { mk_new_line lexbuf; parse_token lexbuf }
  | [' ' '\t' '\r']+         { parse_token lexbuf }
  | '?'                      { QM }
  | '?' identifier as id     { QM_ID id }
  | identifier as i          { try assoc_keyword i with Not_found -> ID i }
  | digit+ as s              { INTEGER s }

  | (digit+ as i) ("" as f) ['e' 'E'] (['-' '+']? as sign (digit+ as exp))
  | (digit+ as i) '.' (digit* as f)
      (['e' 'E'] (['-' '+']? as sign (digit+ as exp)))?
  | (digit* as i) '.' (digit+ as f)
      (['e' 'E'] (['-' '+']? as sign (digit+ as exp)))?
      (* decimal real literals *)
      {
        let v =
          match exp,sign with
          | Some exp,Some "-" ->
            Num.div_num (decimal_number (i^f))
              (Num.power_num (Num.Int 10) (decimal_number exp))
          | Some exp,_ ->
            Num.mult_num (decimal_number (i^f))
              (Num.power_num (Num.Int 10) (decimal_number exp))
          | None,_ -> decimal_number (i^f)
        in
        let v =
          Num.div_num v
            (Num.power_num (Num.Int 10) (Num.num_of_int (String.length f)))
        in
        NUM v
      }

  (* hexadecimal real literals a la C99 (0x..p..) *)
  | "0x" (hexadecimal+ as e) ('.' (hexadecimal* as f))?
      ['p''P'] (['+''-']? as sign) (digit+ as exp)
      {
        let f = match f with None -> "" | Some f -> f in
        let v =
          match sign with
          | "-" ->
            Num.div_num (hexa_number (e^f))
              (Num.power_num (Num.Int 2) (decimal_number exp))
          | _ ->
            Num.mult_num (hexa_number (e^f))
              (Num.power_num (Num.Int 2) (decimal_number exp))
        in
        let v =
          Num.div_num v
            (Num.power_num (Num.Int 16) (Num.num_of_int (String.length f)))
        in
        NUM v
      }
  | "(*"  { parse_comment lexbuf; parse_token lexbuf }
  | "'"   { QUOTE }
  | ","   { COMMA }
  | ";"   { PV }
  | "("   { LEFTPAR }
  | ")"   { RIGHTPAR }
  | ":"   { COLON }
  | "->"  { RIGHTARROW }
  | "<-"  { LEFTARROW }
  | "<->" { LRARROW }
  | "="   { EQUAL }
  | "<"   { LT }
  | "<="  { LE }
  | ">"   { GT }
  | ">="  { GE }
  | "<>"  { NOTEQ }
  | "+"   { PLUS }
  | "-"   { MINUS }
  | "*"   { TIMES }
  | "**." { POWDOT }
  | "**"  { POW }
  | "/"   { SLASH }
  | "%"   { PERCENT }
  | "@"   { AT }
  | "."   { DOT }
  | "#"   { SHARP }
  | "["   { LEFTSQ }
  | "]"   { RIGHTSQ }
  | "{"   { LEFTBR }
  | "}"   { RIGHTBR }
  | "|"   { BAR }
  | "^"   { HAT }
  | "|->" { MAPS_TO }
  | "\""  { parse_string (Buffer.create 1024) lexbuf }
  | eof   { EOF }
  | _ as c {
    let loc = (Lexing.lexeme_start_p lexbuf, Lexing.lexeme_end_p lexbuf) in
    let s = "illegal character: " ^ String.make 1 c in
    Errors.error (Errors.Lexical_error (loc, s))
  }

and parse_comment = parse
  | "*)" { () }
  | "(*" { parse_comment lexbuf; parse_comment lexbuf }
  | '\n' { mk_new_line lexbuf; parse_comment lexbuf }
  | eof  {
    let loc = (Lexing.lexeme_start_p lexbuf, Lexing.lexeme_end_p lexbuf) in
    Errors.error (Errors.Lexical_error (loc, "unterminated comment"))
  }
  | _    { parse_comment lexbuf }

and parse_string str_buf = parse
  | "\"" { STRING (Buffer.contents str_buf) }
  | "\\" (_ as c) {
    Buffer.add_char str_buf (escaped_char c);
    parse_string str_buf lexbuf
  }

  | '\n' {
    mk_new_line lexbuf;
    Buffer.add_char str_buf '\n';
    parse_string str_buf lexbuf
  }

  | eof  {
    let loc = (Lexing.lexeme_start_p lexbuf, Lexing.lexeme_end_p lexbuf) in
    Errors.error (Errors.Lexical_error (loc, "unterminated string"))
  }

  | _ as c {
    Buffer.add_char str_buf c; parse_string str_buf lexbuf
  }

{

  module Parser : Parsers.PARSER_INTERFACE = struct

    let aux aux_fun token lexbuf =
      try
        let res = aux_fun token lexbuf in
        Parsing.clear_parser ();
        res
      with
      (* The --fixed-error flag makes menhir alias
         the exception Error to Parsing.Parse_error *)
      | Parsing.Parse_error ->
        let loc = (Lexing.lexeme_start_p lexbuf, Lexing.lexeme_end_p lexbuf) in
        let lex = Lexing.lexeme lexbuf in
        Parsing.clear_parser ();
        Errors.error (Errors.Syntax_error (loc, lex))

    let file    = aux Native_parser.file_parser    parse_token
    let expr    = aux Native_parser.lexpr_parser   parse_token
    let trigger = aux Native_parser.trigger_parser parse_token
  end

  let register_native () =
    (*register this parser in Input_lang: 3 different extensions recognized *)
    let p = (module Parser : Parsers.PARSER_INTERFACE) in
    Parsers.register_parser ~lang:".ae" p
}
