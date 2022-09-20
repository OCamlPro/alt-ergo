(******************************************************************************)
(*                                                                            *)
(*     The Alt-Ergo theorem prover                                            *)
(*     Copyright (C) 2006-2013                                                *)
(*                                                                            *)
(*     Sylvain Conchon                                                        *)
(*     Evelyne Contejean                                                      *)
(*                                                                            *)
(*     Francois Bobot                                                         *)
(*     Mohamed Iguernelala                                                    *)
(*     Stephane Lescuyer                                                      *)
(*     Alain Mebsout                                                          *)
(*                                                                            *)
(*     CNRS - INRIA - Universite Paris Sud                                    *)
(*                                                                            *)
(*     This file is distributed under the terms of the Apache Software        *)
(*     License version 2.0                                                    *)
(*                                                                            *)
(*  ------------------------------------------------------------------------  *)
(*                                                                            *)
(*     Alt-Ergo: The SMT Solver For Software Verification                     *)
(*     Copyright (C) 2013-2018 --- OCamlPro SAS                               *)
(*                                                                            *)
(*     This file is distributed under the terms of the Apache Software        *)
(*     License version 2.0                                                    *)
(*                                                                            *)
(******************************************************************************)

open Format

(* let x_dpi = Sys.command *)
(*     "(exit `xrdb -query | grep dpi | cut -d':' -f2 | xargs`)" *)
(* let serv_dpi = Sys.command *)
(*     "(exit `xdpyinfo | grep dots | cut -d':' -f2 | cut -d'x' -f1 | xargs`)"*)
(* let scale = x_dpi / serv_dpi *)
(* let scale = if scale > 0 then scale else 1 *)

let config_name = "altgr-ergo.conf"
let filename = Filename.concat (Glib.get_user_config_dir ()) config_name

(* Defaults *)
let window_width = ref 950
let window_height = ref 700
let indent_size = ref 2
let max_indent = ref 80
let max_indents = ref 15
let font_family = ref "monospace"
let font_size = ref 11
let style = ref "tango"
let wrap = ref false

let load () =
  let ic = open_in filename in
  let rec read () =
    try begin match String.split_on_char ':' (input_line ic) with
      | [ "window_width"; value ] ->
        window_width := int_of_string value
      | [ "window_height"; value ] ->
        window_height := int_of_string value
      | [ "indent_size"; value ] ->
        indent_size := int_of_string value
      | [ "max_indent"; value ] ->
        max_indent := int_of_string value
      | [ "max_indents"; value ] ->
        max_indents := int_of_string value
      | [ "font_family"; value ] ->
        font_family := value
      | [ "font_size"; value ] ->
        font_size := int_of_string value
      | [ "style"; value ] ->
        style := value
      | [ "wrap"; value ] ->
        wrap := bool_of_string value
      | _ -> ()
    end; read ()
    with End_of_file -> ()
  in
  read ();
  close_in ic

let write () =
  let oc = open_out filename in
  output_string oc (sprintf "window_width:%d\n" !window_width);
  output_string oc (sprintf "window_height:%d\n" !window_height);
  output_string oc (sprintf "indent_size:%d\n" !indent_size);
  output_string oc (sprintf "max_indent:%d\n" !max_indent);
  output_string oc (sprintf "max_indents:%d\n" !max_indents);
  output_string oc (sprintf "font_family:%s\n" !font_family);
  output_string oc (sprintf "font_size:%s\n" (string_of_int !font_size));
  output_string oc (sprintf "style:%s\n" !style);
  output_string oc (sprintf "wrap:%b\n" !wrap);
  close_out oc

let update_window_size width height =
  window_width := width;
  window_height := height

let update_font_family family =
  font_family := family

let update_font_size size =
  font_size := size

let update_wrap b =
  wrap := b

let init () =
  try
    load ();
  with Sys_error _ -> write ()

let window_width = !window_width
let window_height = !window_height
let indent_size = !indent_size
let max_indent = !max_indent
let max_indents = !max_indents
let font_family = !font_family
let font_size = !font_size
let style = !style
let wrap = !wrap

let not_supported msg =
  AltErgoLib.Printer.print_err
    "%S currently not supported by the GUI" msg;
  assert false
