(******************************************************************************)
(*                                                                            *)
(*     Alt-Ergo: The SMT Solver For Software Verification                     *)
(*     Copyright (C) 2018-2020 --- OCamlPro SAS                               *)
(*                                                                            *)
(*     This file is distributed under the terms of the license indicated      *)
(*     in the file 'License.OCamlPro'. If 'License.OCamlPro' is not           *)
(*     present, please contact us to clarify licensing.                       *)
(*                                                                            *)
(******************************************************************************)

open Format

(*********** Colors ***********)
type style =
  | Normal

  | Bold
  | Bold_off
  | Underline
  | Underline_off

  | FG_Black
  | FG_Red
  | FG_Green
  | FG_Orange
  | FG_Blue
  | FG_Magenta
  | FG_Cyan
  | FG_Default

  | BG_Black
  | BG_Red
  | BG_Green
  | BG_Orange
  | BG_Blue
  | BG_Magenta
  | BG_Cyan
  | BG_Default

(* See https://en.wikipedia.org/wiki/ANSI_escape_code#SGR_parameters
   for some values *)
let to_value = function
  | Normal -> "0"

  | Bold -> "1"
  | Bold_off -> "22"
  | Underline -> "4"
  | Underline_off -> "24"

  | FG_Black -> "30"
  | FG_Red -> "31"
  | FG_Green -> "32"
  | FG_Orange -> "33"
  | FG_Blue -> "34"
  | FG_Magenta -> "35"
  | FG_Cyan -> "36"
  | FG_Default -> "39"

  | BG_Black -> "40"
  | BG_Red -> "41"
  | BG_Green -> "42"
  | BG_Orange -> "43"
  | BG_Blue -> "44"
  | BG_Magenta -> "45"
  | BG_Cyan -> "46"
  | BG_Default -> "49"

let style_of_tag t =
  match Format_shims.get_stag t with
  | "n" -> Normal
  | "bold" -> Bold
  | "/bold" -> Bold_off
  | "underline" -> Underline
  | "/underline" -> Underline_off

  | "fg_black" -> FG_Black
  | "fg_red" -> FG_Red
  | "fg_green" -> FG_Green
  | "fg_orange" -> FG_Orange
  | "fg_blue" -> FG_Blue
  | "fg_magenta" -> FG_Magenta
  | "fg_cyan" -> FG_Cyan
  | "fg_default" -> FG_Default

  | "bg_black" -> BG_Black
  | "bg_red" -> BG_Red
  | "bg_green" -> BG_Green
  | "bg_orange" -> BG_Orange
  | "bg_blue" -> BG_Blue
  | "bg_magenta" -> BG_Magenta
  | "bg_cyan" -> BG_Cyan
  | "bg_default" -> BG_Default

  | _ -> raise Not_found

let close_tag = function
  | Bold -> Bold_off
  | Underline -> Underline_off
  | FG_Black | FG_Red | FG_Green | FG_Default -> FG_Default
  | BG_Black | BG_Red | BG_Green | BG_Default -> BG_Default
  | _ -> Normal

let start_stag t =
  try Printf.sprintf "\x1B[%sm" (to_value (style_of_tag t))
  with Not_found -> ""

let stop_stag t =
  try Printf.sprintf "\x1B[%sm" (to_value (close_tag (style_of_tag t)))
  with Not_found -> ""

let add_colors formatter =
  pp_set_tags formatter true;
  let old_fs = Format_shims.pp_get_formatter_stag_functions formatter () in
  Format_shims.pp_set_formatter_stag_functions formatter
    (Format_shims.update_stag_functions old_fs start_stag stop_stag)

let init_colors () =
  add_colors (Options.get_fmt_wrn ());
  add_colors (Options.get_fmt_err ());
  add_colors (Options.get_fmt_dbg ())

(************** Output Format *************)
(* let pp_smt =
   let smt = match Options.get_output_format () with
    | Smtlib2 -> true
    | Native | Why3 | Unknown _ -> false
   in sprintf "%s" (if smt then "; " else "")
*)
let add_smt formatter =
  let old_fs = Format_shims.pp_get_formatter_out_functions formatter () in
  let out_newline () = old_fs.out_string "\n; " 0 3 in
  Format_shims.pp_set_formatter_out_functions formatter
    { old_fs with out_newline }

let init_output_format () =
  match Options.get_output_format () with
  | Smtlib2 ->
    add_smt (Options.get_fmt_err ());
    add_smt (Options.get_fmt_wrn ());
    add_smt (Options.get_fmt_dbg ())
  (*   add_smt (Options.get_fmt_std ()) *)
  | Native | Why3 | Unknown _ -> ()


(************** Printers *************)
let print_std s =
  fprintf (Options.get_fmt_std ()) s

let print_err ?(header=true) ?(error=true) s =
  if error then begin
    if header then
      fprintf (Options.get_fmt_err ())
        "@[<v 7>@{<fg_red>@{<bold>[Error]@}@}";
    fprintf (Options.get_fmt_err ()) s
  end
  else ifprintf err_formatter s

let print_wrn ?(header=true) ?(warning=true) s =
  if warning then begin
    if header then
      fprintf (Options.get_fmt_wrn ())
        "@[<v 9>@{<fg_orange>@{<bold>[Warning]@}@}" ;
    fprintf (Options.get_fmt_wrn ()) s
  end
  else ifprintf err_formatter s

let print_dbg ?(header=true) ?(debug=true)
    ?(module_name="") ?(function_name="") s =
  if debug then begin
    if header then begin
      let fname =if String.equal function_name ""
        then ""
        else sprintf "[%s]" function_name
      in
      let mname =if String.equal module_name ""
        then ""
        else sprintf "[%s]" module_name
      in
      fprintf (Options.get_fmt_dbg ())
        "@{<fg_blue>@{<bold>[Debug]%s%s@}@}@,@[<v 0>"
        mname fname;
    end;
    fprintf (Options.get_fmt_dbg ()) s
  end
  else ifprintf err_formatter s

let flush_dbg ?(debug=true) () =
  if debug then fprintf (Options.get_fmt_dbg ()) "@."

let print_vrb ?verbose:(v=true) s =
  if v then
    print_dbg s
  else ifprintf err_formatter s

let print_fmt fmt s =
  fprintf fmt s

(* Utils *)

let pp_sep_nospace fmt () = fprintf fmt ""

let pp_list_no_space f fmt l =
  pp_print_list ~pp_sep:pp_sep_nospace f fmt l
