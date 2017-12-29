(******************************************************************************)
(*                                                                            *)
(*     Alt-Ergo: The SMT Solver For Software Verification                     *)
(*     Copyright (C) 2013-2017 --- OCamlPro SAS                               *)
(*                                                                            *)
(*     This file is distributed under the terms of the license indicated      *)
(*     in the file 'License.OCamlPro'. If 'License.OCamlPro' is not           *)
(*     present, please contact us to clarify licensing.                       *)
(*                                                                            *)
(******************************************************************************)

open Options
open Format

let current = ref (module Fun_sat : Sat_solver_sig.S)

let initialized = ref false

let set_current sat =
  if use_satml() then
    current := sat

let load_current_sat () =
  match sat_plugin () with
  | "" ->
    if debug_sat () then eprintf "[Dynlink] Using Fun_sat solver@."

  | path ->
    if debug_sat () then
      eprintf "[Dynlink] Loading the SAT-solver in %s ...@." path;
    try
      MyDynlink.loadfile path;
      if debug_sat () then  eprintf "Success !@.@."
    with
    | MyDynlink.Error m1 ->
      if debug_sat() then begin
        eprintf
          "[Dynlink] Loading the SAT-solver in plugin \"%s\" failed!@."
          path;
        Format.eprintf ">> Failure message: %s@.@." (MyDynlink.error_message m1);
      end;
      let prefixed_path = sprintf "%s/%s" Config.pluginsdir path in
      if debug_sat () then
        eprintf "[Dynlink] Loading the SAT-solver in %s ... with prefix %s@."
          path Config.pluginsdir;
      try
        MyDynlink.loadfile prefixed_path;
        if debug_sat () then  eprintf "Success !@.@."
      with
      | MyDynlink.Error m2 ->
        if not (debug_sat()) then begin
          eprintf
            "[Dynlink] Loading the SAT-solver in plugin \"%s\" failed!@."
            path;
          Format.eprintf ">> Failure message: %s@.@."
            (MyDynlink.error_message m1);
        end;
        eprintf
          "[Dynlink] Trying to load the plugin from \"%s\" failed too!@."
          prefixed_path;
        Format.eprintf ">> Failure message: %s@.@." (MyDynlink.error_message m2);
        exit 1

let get_current () =
  if not !initialized then
    begin
      load_current_sat ();
      initialized := true;
    end;
  !current
