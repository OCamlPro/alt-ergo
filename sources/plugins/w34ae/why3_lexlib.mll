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

{
  open Lexing

  (* lexical errors *)

  exception UnterminatedComment
  exception UnterminatedString

  (*let () = Why3_exn_printer.register (fun fmt e -> match e with
    | UnterminatedComment -> fprintf fmt "unterminated comment"
    | UnterminatedString -> fprintf fmt "unterminated string"
    | _ -> raise e)*)

  let newline lexbuf =
    let pos = lexbuf.lex_curr_p in
    lexbuf.lex_curr_p <-
      { pos with pos_lnum = pos.pos_lnum + 1; pos_bol = pos.pos_cnum }

  let string_start_loc = ref Why3_loc.dummy_position
  let string_buf = Buffer.create 1024

  let comment_start_loc = ref Why3_loc.dummy_position

  let char_for_backslash = function
    | 'n' -> '\n'
    | 't' -> '\t'
    | c -> c

}

let newline = '\n'

rule comment = parse
  | "(*)"
      { comment lexbuf }
  | "*)"
      { () }
  | "(*"
      { comment lexbuf; comment lexbuf }
  | newline
      { newline lexbuf; comment lexbuf }
  | eof
      { raise (Why3_loc.Why3_located (!comment_start_loc, UnterminatedComment)) }
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
  let loc lb = (lexeme_start_p lb, lexeme_end_p lb)

  let comment lexbuf = comment_start_loc := loc lexbuf; comment lexbuf

  let string lexbuf = string_start_loc := loc lexbuf; string lexbuf

  let update_loc lexbuf file line chars =
    let pos = lexbuf.lex_curr_p in
    let new_file = match file with None -> pos.pos_fname | Some s -> s in
    lexbuf.lex_curr_p <-
      { pos with
          pos_fname = new_file;
          pos_lnum = line;
          pos_bol = pos.pos_cnum - chars;
      }

  let remove_leading_plus s =
    let n = String.length s in
    if n > 0 && s.[0] = '+' then String.sub s 1 (n-1) else s

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

}
