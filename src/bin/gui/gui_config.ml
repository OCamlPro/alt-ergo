(*********************************************************************************)
(*                                                                               *)
(*     Alt-Ergo: The SMT Solver For Software Verification                        *)
(*     Copyright (C) --- OCamlPro SAS                                            *)
(*                                                                               *)
(*     This software is governed by the CeCILL  license under French law and     *)
(*     abiding by the rules of distribution of free software.  You can  use,     *)
(*     modify and/ or redistribute the software under the terms of the CeCILL    *)
(*     license as circulated by CEA, CNRS and INRIA at the following URL         *)
(*     "http://www.cecill.info".                                                 *)
(*                                                                               *)
(*     As a counterpart to the access to the source code and  rights to copy,    *)
(*     modify and redistribute granted by the license, users are provided only   *)
(*     with a limited warranty  and the software's author,  the holder of the    *)
(*     economic rights,  and the successive licensors  have only  limited        *)
(*     liability.                                                                *)
(*                                                                               *)
(*     In this respect, the user's attention is drawn to the risks associated    *)
(*     with loading,  using,  modifying and/or developing or reproducing the     *)
(*     software by the user in light of its specific status of free software,    *)
(*     that may mean  that it is complicated to manipulate,  and  that  also     *)
(*     therefore means  that it is reserved for developers  and  experienced     *)
(*     professionals having in-depth computer knowledge. Users are therefore     *)
(*     encouraged to load and test the software's suitability as regards their   *)
(*     requirements in conditions enabling the security of their systems and/or  *)
(*     data to be ensured and,  more generally, to use and operate it in the     *)
(*     same conditions as regards security.                                      *)
(*                                                                               *)
(*     The fact that you are presently reading this means that you have had      *)
(*     knowledge of the CeCILL license and that you accept its terms.            *)
(*                                                                               *)
(*     ------------------------------------------------------------------------  *)
(*                                                                               *)
(*     This is a free release of Alt-Ergo under the terms of CeCILL license.     *)
(*     The latest releases of Alt-Ergo are distributed under the terms of        *)
(*     OCamlPro Non-Commercial Purpose License, version 1.                       *)
(*                                                                               *)
(*     As an exception, Alt-Ergo Club members at the Gold level can              *)
(*     use this file under the terms of the Apache Software License              *)
(*     version 2.0.                                                              *)
(*                                                                               *)
(*     ------------------------------------------------------------------------  *)
(*                                                                               *)
(*     The Alt-Ergo theorem prover                                               *)
(*                                                                               *)
(*     Sylvain Conchon, Evelyne Contejean, Francois Bobot                        *)
(*     Mohamed Iguernelala, Stephane Lescuyer, Alain Mebsout                     *)
(*                                                                               *)
(*     CNRS - INRIA - Universite Paris Sud                                       *)
(*                                                                               *)
(*     ------------------------------------------------------------------------  *)
(*                                                                               *)
(*     More details can be found in the directory licenses/                      *)
(*                                                                               *)
(*********************************************************************************)

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
