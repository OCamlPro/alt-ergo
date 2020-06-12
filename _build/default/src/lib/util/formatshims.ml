(******************************************************************************)
(*                                                                            *)
(*     Alt-Ergo: The SMT Solver For Software Verification                     *)
(*     Copyright (C) 2018-2020 --- OCamlPro SAS                               *)
(*                                                                            *)
(*     This file is distributed under the terms of the license indicated      *)
(*     in the file 'License.OCamlPro'. If 'License.OCamlPro' is not           *)
(*     present, please contact us to clarify licensing.                       *)
(*                                                                            *)
(*     Some parts of this file are exctracted from the                        *)
(*     projectOcaml-containers :                                              *)
(* https://github.com/c-cube/ocaml-containers/blob/master/src/core/mkshims.ml *)
(*     Thanks to Simon Cruanes                                                *)
(*                                                                            *)
(******************************************************************************)

module C = Configurator.V1

let write_file f s =
  let out = open_out f in
  output_string out s; flush out; close_out out

let shims_fmt_pre_408 = "
include Format

let pp_open_stag = pp_open_tag
let open_stag = open_tag
let pp_close_stag = pp_close_tag
let close_stag = close_tag

type formatter_stag_functions = formatter_tag_functions

let pp_get_formatter_stag_functions = pp_get_formatter_tag_functions
let get_formatter_stag_functions = get_formatter_tag_functions
let pp_set_formatter_stag_functions = pp_set_formatter_tag_functions
let set_formatter_stag_functions = set_formatter_tag_functions

let get_stag s = s

let update_stag_functions funs start_stag stop_stag =
  let open Format in
  { funs with
    mark_open_tag = start_stag;
    mark_close_tag = stop_stag }

"

let shims_fmt_post_408 = "
include Format

let get_stag = function
  | String_tag s -> s
  | _ -> raise Not_found

let update_stag_functions funs start_stag stop_stag =
  let open Format in
  { funs with
    mark_open_stag = start_stag;
    mark_close_stag = stop_stag }
"

let () =
  C.main ~name:"mkshims" (fun c ->
      let version = C.ocaml_config_var_exn c "version" in
      let major, minor =
        Scanf.sscanf version "%u.%u" (fun maj min -> maj, min) in
      write_file "format_shims.ml"
        (if (major, minor) >= (4,8)
         then shims_fmt_post_408
         else shims_fmt_pre_408);
    )
