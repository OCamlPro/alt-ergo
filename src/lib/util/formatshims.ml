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
