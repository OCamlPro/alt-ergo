(******************************************************************************)
(*                                                                            *)
(*     Alt-Ergo: The SMT Solver For Software Verification                     *)
(*     Copyright (C) 2013-2018 --- OCamlPro SAS                               *)
(*                                                                            *)
(*     This file is distributed under the terms of the license indicated      *)
(*     in the file 'License.OCamlPro'. If 'License.OCamlPro' is not           *)
(*     present, please contact us to clarify licensing.                       *)
(*                                                                            *)
(******************************************************************************)

(** A wrapper of the Dynlink module: we use Dynlink except when we want to
    generate a static (native) binary **)

[@@@ocaml.warning "-60"]
module DummyDL = struct

  type error = string

  [@@@ocaml.warning "-38"]
  exception Error of error

  [@@@ocaml.warning "-32"]
  let error_message s = s

  [@@@ocaml.warning "-32"]
  let loadfile _ = ()

end

include Dynlink

let load fmt get_verbose p msg =
  if get_verbose then
    Format.fprintf fmt "[Dynlink] Loading the %s in %S ...@." msg p;
  try
    loadfile p;
    if get_verbose then Format.fprintf fmt "Success !@.@."
  with
  | Error m1 ->
    if get_verbose then begin
      Format.fprintf fmt "[Dynlink] Loading the %s in plugin %S failed!@."
        msg p;
      Format.fprintf fmt ">> Failure message: %s@.@." (error_message m1);
    end;
    let pp = Format.sprintf "%s/%s" Config.pluginsdir p in
    if get_verbose then
      Format.fprintf fmt "[Dynlink] Loading the %s in %S ... with prefix %S@."
        msg p Config.pluginsdir;
    try
      loadfile pp;
      if get_verbose then Format.fprintf fmt "Success !@.@."
    with
    | Error m2 ->
      if not get_verbose then begin
        Format.fprintf fmt
          "[Dynlink] Loading the %s in plugin %S failed!@." msg p;
        Format.fprintf fmt ">> Failure message: %s@.@." (error_message m1);
      end;
      Errors.run_error
        (Dynlink_error
           (Format.sprintf
              "Trying to load the plugin from %S failed too!@. \
               >> Failure message: %s@.@." pp (error_message m2)))
