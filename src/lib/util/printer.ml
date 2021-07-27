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
  if Options.get_output_with_colors () then begin
    add_colors (Options.get_fmt_std ());
    add_colors (Options.get_fmt_wrn ());
    add_colors (Options.get_fmt_err ());
    add_colors (Options.get_fmt_dbg ())
  end

(************** Output Format *************)
let clean_dbg_print = ref true
let clean_wrn_print = ref true

let pp_smt clean_print =
  let smt = match Options.get_output_format () with
    | Smtlib2 -> true
    | Native | Why3 | Unknown _ -> false
  in sprintf
    (if smt && !clean_print then
       begin clean_print := false; "@,; " end
     else "")

let pp_std_smt () =
  match !clean_dbg_print, !clean_wrn_print with
  | true, true -> ()
  | false, true ->
    clean_dbg_print := true;
    fprintf (Options.get_fmt_std ()) "@,"
  | true, false ->
    clean_wrn_print := true;
    fprintf (Options.get_fmt_std ()) "@,"
  | false, false ->
    clean_dbg_print := true;
    clean_wrn_print := true;
    fprintf (Options.get_fmt_std ()) "@,"

let add_smt formatter =
  let old_fs = Format_shims.pp_get_formatter_out_functions formatter () in
  let out_newline () = old_fs.out_string "\n; " 0 3 in
  Format_shims.pp_set_formatter_out_functions formatter
    { old_fs with out_newline }

let remove_formatting formatter =
  let old_fs = Format_shims.pp_get_formatter_out_functions formatter () in
  let out_newline () = old_fs.out_string "" 0 0 in
  let out_spaces _n = old_fs.out_spaces 0 in
  Format.pp_set_formatter_out_functions formatter
    { old_fs with out_newline; out_spaces }

(* This function is used to force a newline when the option removing the
   formatting is enable *)
let force_new_line formatter =
  if not (Options.get_output_with_formatting ()) then
    let old_fs = Format_shims.pp_get_formatter_out_functions formatter () in
    let out_newline () = old_fs.out_string "\n" 0 1 in
    Format_shims.pp_set_formatter_out_functions formatter
      { old_fs with out_newline };
    Format.fprintf formatter "@.";
    remove_formatting formatter

let init_output_format () =
  match Options.get_output_format () with
  | Smtlib2 ->
    add_smt (Options.get_fmt_wrn ());
    add_smt (Options.get_fmt_dbg ())
  | Native | Why3 | Unknown _ -> ()


(************** Printers *************)
let flush fmt = Format.fprintf fmt "@."

let print_std ?(flushed=true) s =
  pp_std_smt ();
  let fmt = Options.get_fmt_std () in
  if flushed || Options.get_output_with_forced_flush ()
  then kfprintf flush fmt s else fprintf fmt s

let print_err ?(flushed=true) ?(header=(Options.get_output_with_headers ()))
    ?(error=true) s =
  if error then begin
    let fmt = Options.get_fmt_err () in
    fprintf fmt "@[<v 0>";
    if header then
      if Options.get_output_with_colors () then
        fprintf fmt "@[<v 7>@{<fg_red>@{<bold>[Error]@}@}"
      else
        fprintf fmt "@[<v 7>[Error]";
    if flushed || Options.get_output_with_forced_flush ()
    then kfprintf flush fmt s else fprintf fmt s
  end
  else ifprintf err_formatter s

let print_wrn ?(flushed=true) ?(header=(Options.get_output_with_headers ()))
    ?(warning=true) s =
  if Options.get_warning_as_error () then
    print_err ~flushed ~header ~error:warning s
  else
  if warning then begin
    let fmt = Options.get_fmt_wrn () in
    fprintf fmt "@[<v 0>%s" (pp_smt clean_wrn_print);
    if header then
      if Options.get_output_with_colors () then
        fprintf fmt "@[<v 9>@{<fg_orange>@{<bold>[Warning]@}@} "
      else
        fprintf fmt "@[<v 9>[Warning] " ;
    if flushed || Options.get_output_with_forced_flush ()
    then kfprintf flush fmt s else fprintf fmt s
  end
  else ifprintf err_formatter s

let print_dbg ?(flushed=true) ?(header=(Options.get_output_with_headers ()))
    ?(module_name="") ?(function_name="") s =
  let fmt = Options.get_fmt_dbg () in
  fprintf fmt "@[<v 0>%s" (pp_smt clean_dbg_print);
  if header then begin
    let fname =
      if String.equal function_name ""
      then ""
      else sprintf "[%s]" function_name
    in
    let mname =
      if String.equal module_name ""
      then ""
      else sprintf "[%s]" module_name
    in
    (* we force a newline to split the print at every print with header *)
    force_new_line fmt;
    if Options.get_output_with_colors () then
      fprintf fmt
        "@{<fg_blue>@{<bold>[Debug]%s%s@}@}@,@[<v 0>"
        mname fname
    else
      fprintf fmt
        "[Debug]%s%s@,@[<v 0>" mname fname
  end;
  if flushed || Options.get_output_with_forced_flush ()
  then kfprintf flush fmt s else fprintf fmt s


let print_fmt ?(flushed=true) fmt s =
  pp_std_smt ();
  if flushed || Options.get_output_with_forced_flush () then
    kfprintf flush fmt s else fprintf fmt s

(* Utils *)

let pp_sep_nospace fmt () = fprintf fmt ""

let pp_list_no_space f fmt l =
  pp_print_list ~pp_sep:pp_sep_nospace f fmt l


(******** Status printers *********)
let status_time t =
  match t with
    None -> ""
  | Some t -> sprintf " (%2.4f)" t

let status_steps s =
  match s with
    None -> ""
  | Some s -> sprintf " (%d steps)" s

let status_goal g =
  match g with
    None -> ""
  | Some g -> sprintf " (goal %s)" g

let print_status_loc fmt loc =
  match loc with
  | None -> ()
  | Some loc ->
    if Options.get_answers_with_locs () then
      fprintf fmt "%a " Loc.report loc

let print_status_value fmt (v,color) =
  if Options.get_output_with_colors () then
    fprintf fmt  "@{<%s>@{<bold>%s@}@}" color v
  else
    fprintf fmt "%s" v

let print_status ?(validity_mode=true)
    ?(formatter=Options.get_fmt_std ())
    (validity_status,unsat_status,color) loc time steps goal =
  pp_std_smt ();
  let native_output_fmt, comment_if_smt2 =
    if validity_mode then formatter, ""
    else (Options.get_fmt_dbg ()), (pp_smt clean_dbg_print)
  in
  (* print validity status. Commented and in debug fmt if in unsat mode *)
  fprintf native_output_fmt
    "%s%a%a%s%s%s@."
    comment_if_smt2
    print_status_loc loc
    print_status_value (validity_status,color)
    (status_time time)
    (status_steps steps)
    (status_goal goal);
  if not validity_mode && String.length unsat_status > 0 then begin
    pp_std_smt ();
    (* print SMT2 status if not in validity mode *)
    fprintf formatter "%a@." print_status_value (unsat_status,color)
  end

let print_status_unsat ?(validity_mode=true) loc
    time steps goal =
  print_status ~validity_mode ("Valid","unsat","fg_green") loc
    time steps goal

let print_status_sat ?(validity_mode=true) loc
    time steps goal =
  print_status ~validity_mode ("Invalid","sat","fg_blue") loc
    time steps goal

let print_status_inconsistent ?(validity_mode=true) loc
    time steps goal =
  print_status ~validity_mode
    ~formatter:(Options.get_fmt_dbg ())
    ("Inconsistent assumption","","fg_red") loc
    time steps goal

let print_status_unknown ?(validity_mode=true) loc
    time steps goal =
  print_status ~validity_mode
    ("I don't know","unknown","fg_cyan") loc
    time steps goal

let print_status_timeout ?(validity_mode=true) loc
    time steps goal =
  print_status ~validity_mode
    ("Timeout","timeout","fg_orange") loc
    time steps goal

let print_status_preprocess ?(validity_mode=true)
    time steps =
  print_status ~validity_mode
    ~formatter:(Options.get_fmt_dbg ())
    ("Preprocessing","","fg_magenta") None
    time steps None
