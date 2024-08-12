(**************************************************************************)
(*                                                                        *)
(*     Alt-Ergo: The SMT Solver For Software Verification                 *)
(*     Copyright (C) --- OCamlPro SAS                                     *)
(*                                                                        *)
(*     This file is distributed under the terms of OCamlPro               *)
(*     Non-Commercial Purpose License, version 1.                         *)
(*                                                                        *)
(*     As an exception, Alt-Ergo Club members at the Gold level can       *)
(*     use this file under the terms of the Apache Software License       *)
(*     version 2.0.                                                       *)
(*                                                                        *)
(*     ---------------------------------------------------------------    *)
(*                                                                        *)
(*     The Alt-Ergo theorem prover                                        *)
(*                                                                        *)
(*     Sylvain Conchon, Evelyne Contejean, Francois Bobot                 *)
(*     Mohamed Iguernelala, Stephane Lescuyer, Alain Mebsout              *)
(*                                                                        *)
(*     CNRS - INRIA - Universite Paris Sud                                *)
(*                                                                        *)
(*     ---------------------------------------------------------------    *)
(*                                                                        *)
(*     More details can be found in the directory licenses/               *)
(*                                                                        *)
(**************************************************************************)

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

let get_stag = function
  | Format.String_tag s -> s
  | _ -> raise Not_found

let style_of_tag t =
  match get_stag t with
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

let update_stag_functions funs start_stag stop_stag =
  let open Format in
  { funs with
    mark_open_stag = start_stag;
    mark_close_stag = stop_stag }

let add_colors formatter =
  Format.pp_set_tags formatter true;
  let old_fs = Format.pp_get_formatter_stag_functions formatter () in
  Format.pp_set_formatter_stag_functions formatter
    (update_stag_functions old_fs start_stag stop_stag)

let init_colors () =
  if Options.get_output_with_colors () then begin
    add_colors (Options.Output.get_fmt_regular ());
    add_colors (Options.Output.get_fmt_diagnostic ())
  end

(************** Output Format *************)
let clean_dbg_print = ref true
let clean_wrn_print = ref true

let pp_smt clean_print =
  let smt = match Options.get_output_format () with
    | Smtlib2 _ -> true
    | Native | Why3 | Unknown _ -> false
  in Format.sprintf
    (if smt && !clean_print then
       begin clean_print := false; "@,; " end
     else "")

let pp_std_smt () =
  match !clean_dbg_print, !clean_wrn_print with
  | true, true -> ()
  | false, true ->
    clean_dbg_print := true;
    Format.fprintf (Options.Output.get_fmt_regular ()) "@,"
  | true, false ->
    clean_wrn_print := true;
    Format.fprintf (Options.Output.get_fmt_regular ()) "@,"
  | false, false ->
    clean_dbg_print := true;
    clean_wrn_print := true;
    Format.fprintf (Options.Output.get_fmt_regular ()) "@,"

let add_smt formatter =
  let old_fs = Format.pp_get_formatter_out_functions formatter () in
  let out_newline () = old_fs.out_string "\n; " 0 3 in
  Format.pp_set_formatter_out_functions formatter
    { old_fs with out_newline }

let remove_formatting formatter =
  let old_fs = Format.pp_get_formatter_out_functions formatter () in
  let out_newline () = old_fs.out_string "" 0 0 in
  let out_spaces _n = old_fs.out_spaces 0 in
  Format.pp_set_formatter_out_functions formatter
    { old_fs with out_newline; out_spaces }

(* This function is used to force a newline when the option removing the
   formatting is enable *)
let force_new_line formatter =
  if not (Options.get_output_with_formatting ()) then
    let old_fs = Format.pp_get_formatter_out_functions formatter () in
    let out_newline () = old_fs.out_string "\n" 0 1 in
    Format.pp_set_formatter_out_functions formatter
      { old_fs with out_newline };
    Format.fprintf formatter "@.";
    remove_formatting formatter

let init_output_format () =
  match Options.get_output_format () with
  | Smtlib2 _ ->
    add_smt (Options.Output.get_fmt_diagnostic ())
  | Native | Why3 | Unknown _ -> ()


(************** Printers *************)
let flush fmt = Format.fprintf fmt "@."

let print_std ?(flushed=true) s =
  pp_std_smt ();
  let fmt = Options.Output.get_fmt_regular () in
  if flushed || Options.get_output_with_forced_flush ()
  then Format.kfprintf flush fmt s else Format.fprintf fmt s

let print_err ?(flushed=true) ?(header=(Options.get_output_with_headers ()))
    ?(error=true) s =
  if error then begin
    let fmt = Options.Output.get_fmt_diagnostic () in
    Format.fprintf fmt "@[<v 0>";
    if header then
      if Options.get_output_with_colors () then
        Format.fprintf fmt "@[<v 7>@{<fg_red>@{<bold>[Error]@}@}"
      else
        Format.fprintf fmt "@[<v 7>[Error]";
    if flushed || Options.get_output_with_forced_flush ()
    then Format.kfprintf flush fmt s else Format.fprintf fmt s
  end
  else Format.ifprintf Format.err_formatter s

let print_wrn ?(flushed=true) ?(header=(Options.get_output_with_headers ()))
    ?(warning=true) s =
  if Options.get_warning_as_error () then
    print_err ~flushed ~header ~error:warning s
  else
  if warning then begin
    let fmt = Options.Output.get_fmt_diagnostic () in
    Format.fprintf fmt "@[<v 0>%s" (pp_smt clean_wrn_print);
    if header then
      if Options.get_output_with_colors () then
        Format.fprintf fmt "@[<v 10>@{<fg_orange>@{<bold>[Warning]@}@} "
      else
        Format.fprintf fmt "@[<v 10>[Warning] " ;
    if flushed || Options.get_output_with_forced_flush ()
    then Format.kfprintf flush fmt s else Format.fprintf fmt s
  end
  else Format.ifprintf Format.err_formatter s

let print_dbg ?(flushed=true) ?(header=(Options.get_output_with_headers ()))
    ?(module_name="") ?(function_name="") s =
  let fmt = Options.Output.get_fmt_diagnostic () in
  if header then
    Format.fprintf fmt "@[%s" (pp_smt clean_dbg_print)
  else
    Format.fprintf fmt "@[<v 0>%s" (pp_smt clean_dbg_print);
  if header then begin
    let fname =
      if String.equal function_name ""
      then ""
      else Format.sprintf "[%s]" function_name
    in
    let mname =
      if String.equal module_name ""
      then ""
      else Format.sprintf "[%s]" module_name
    in
    (* we force a newline to split the print at every print with header *)
    force_new_line fmt;
    if Options.get_output_with_colors () then
      Format.fprintf fmt
        "@{<fg_blue>@{<bold>[Debug]%s%s@}@}@ @[<v 0>"
        mname fname
    else
      Format.fprintf fmt
        "[Debug]%s%s@ @[<v 0>" mname fname
  end;
  if flushed || Options.get_output_with_forced_flush ()
  then Format.kfprintf flush fmt s else Format.fprintf fmt s


let print_fmt ?(flushed=true) fmt s =
  pp_std_smt ();
  if flushed || Options.get_output_with_forced_flush () then
    Format.kfprintf flush fmt s else Format.fprintf fmt s

(* Utils *)

let pp_sep_nospace fmt () = Format.fprintf fmt ""

let pp_list_no_space f fmt l =
  Format.pp_print_list ~pp_sep:pp_sep_nospace f fmt l

let pp_sep_space fmt () = Format.fprintf fmt " "

let pp_list_space f fmt l =
  Format.pp_print_list ~pp_sep:pp_sep_space f fmt l

(******** Status printers *********)
let status_time t =
  match t with
    None -> ""
  | Some t -> Format.sprintf " (%2.4f)" t

let status_steps s =
  match s with
    None -> ""
  | Some s -> Format.sprintf " (%d steps)" s

let status_goal g =
  match g with
    None -> ""
  | Some g -> Format.sprintf " (goal %s)" g

let print_status_loc fmt loc =
  match loc with
  | None -> ()
  | Some loc ->
    if Options.get_answers_with_locs () then
      Format.fprintf fmt "%a " Loc.report loc

let print_status_value fmt (v,color) =
  if Options.get_output_with_colors () then
    Format.fprintf fmt  "@{<%s>@{<bold>%s@}@}" color v
  else
    Format.fprintf fmt "%s" v

let print_status ?(validity_mode=true)
    ?(formatter=Options.Output.get_fmt_regular ())
    (validity_status,unsat_status,color) loc time steps goal =
  pp_std_smt ();
  let native_output_fmt, comment_if_smt2 =
    if validity_mode then formatter, ""
    else (Options.Output.get_fmt_diagnostic ()), (pp_smt clean_dbg_print)
  in
  (* print validity status. Commented and in debug fmt if in unsat mode *)
  Format.fprintf native_output_fmt
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
    Format.fprintf formatter "%a@." print_status_value (unsat_status,color)
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
    ~formatter:(Options.Output.get_fmt_diagnostic ())
    ("Inconsistent assumption","","fg_red") loc
    time steps goal

let print_status_unknown ?(validity_mode=true) loc
    time steps goal =
  print_status ~validity_mode
    ("I don't know","unknown","fg_cyan") loc
    time steps goal

(* TODO: The timeout answer doesn't exist in the SMT-LIB standard.
   See issue https://github.com/OCamlPro/alt-ergo/issues/834. *)
let print_status_timeout ?(validity_mode=true) loc
    time steps goal =
  print_status ~validity_mode
    ("Timeout","unknown","fg_orange") loc
    time steps goal

let print_status_preprocess ?(validity_mode=true)
    time steps =
  print_status ~validity_mode
    ~formatter:(Options.Output.get_fmt_diagnostic ())
    ("Preprocessing","","fg_magenta") None
    time steps None

let print_smtlib_err ?(flushed=true) s =
  (* The smtlib error messages are printed on the regular output. *)
  pp_std_smt ();
  let fmt = Options.Output.get_fmt_regular () in
  let k fmt =
    if flushed || Options.get_output_with_forced_flush () then
      Format.fprintf fmt "\")@."
    else
      Format.fprintf fmt "\")"
  in
  Format.fprintf fmt "(error \"";
  Format.kfprintf k fmt s

let pp_source ppf src =
  let name = Logs.Src.doc src in
  Fmt.pf ppf "%s" name

let pp_smtlib_header ppf level =
  match (level : Logs.level) with
  | App | Info -> ()
  | Debug | Warning | Error -> Fmt.pf ppf "; "

let reporter =
  let report src level ~over k msgf =
    let k _ = over (); k () in
    let with_header h _tags k fmt =
      if Logs.Src.equal src Logs.default then
        Fmt.kpf k (Options.Output.get_fmt_regular ())
          ("%a@[" ^^ fmt ^^ "@]@.")
          pp_smtlib_header level
      else if Logs.Src.equal src Sources.model then
        Fmt.kpf k (Options.Output.get_fmt_models ())
          ("@[" ^^ fmt ^^ "@]@.")
      else
        let ppf = Options.Output.get_fmt_diagnostic () in
        if Options.get_output_with_colors () then
          Fmt.set_style_renderer ppf `Ansi_tty;
        Fmt.kpf k ppf ("%a[%a] @[" ^^ fmt ^^ "@]@.")
          Logs_fmt.pp_header (level, h)
          pp_source src
    in
    msgf @@ fun ?header ?tags fmt -> with_header header tags k fmt
  in
  { Logs.report }
