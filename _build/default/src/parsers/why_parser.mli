
(* The type of tokens. *)

type token = 
  | XOR
  | WITH
  | VOID
  | UNIT
  | TYPE
  | TRUE
  | TIMES
  | THEORY
  | THEN
  | STRING of (string)
  | SLASH
  | SHARP
  | RIGHTSQ
  | RIGHTPAR
  | RIGHTBR
  | RIGHTARROW
  | REWRITING
  | REAL
  | QUOTE
  | QM_ID of (string)
  | QM
  | PV
  | PROP
  | PRED
  | POWDOT
  | POW
  | PLUS
  | PERCENT
  | OR
  | OF
  | NUM of (Num.num)
  | NOTEQ
  | NOT
  | MINUS
  | MATCH
  | MAPS_TO
  | LT
  | LRARROW
  | LOGIC
  | LET
  | LEFTSQ
  | LEFTPAR
  | LEFTBR
  | LEFTARROW
  | LE
  | INTEGER of (string)
  | INT
  | IN
  | IF
  | ID of (string)
  | HAT
  | GT
  | GOAL
  | GE
  | FUNC
  | FORALL
  | FALSE
  | EXTENDS
  | EXISTS
  | EQUAL
  | EOF
  | END
  | ELSE
  | DOT
  | DISTINCT
  | CUT
  | COMMA
  | COLON
  | CHECK
  | CASESPLIT
  | BOOL
  | BITV
  | BAR
  | AXIOM
  | AT
  | AND
  | AC

(* This exception is raised by the monolithic API functions. *)

exception Error

(* The monolithic API. *)

val trigger_parser: (Lexing.lexbuf -> token) -> Lexing.lexbuf -> (AltErgoLib.Parsed.lexpr list * bool)

val lexpr_parser: (Lexing.lexbuf -> token) -> Lexing.lexbuf -> (AltErgoLib.Parsed.lexpr)

val file_parser: (Lexing.lexbuf -> token) -> Lexing.lexbuf -> (AltErgoLib.Parsed.file)
