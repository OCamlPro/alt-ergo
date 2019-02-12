(******************************************************************************)
(*                                                                            *)
(*     Alt-Ergo: The SMT Solver For Software Verification                     *)
(*     Copyright (C) 2013-2018 --- OCamlPro SAS                               *)
(*                                                                            *)
(*     This file is distributed under the terms of the Apache Software        *)
(*     License version 2.0                                                    *)
(*                                                                            *)
(******************************************************************************)

open AltErgoLib
open Options
open Format

let () =
  List.iter
    (fun p ->
       if verbose () then eprintf "[Dynlink] Loading the parser in %S ...@." p;
       try
         MyDynlink.loadfile p;
         if verbose () then  eprintf "Success !@.@."
       with
       | MyDynlink.Error m1 ->
         if verbose() then begin
           eprintf "[Dynlink] Loading the parser in plugin %S failed!@." p;
           eprintf ">> Failure message: %s@.@." (MyDynlink.error_message m1);
         end;

         let pp = sprintf "%s/%s" Config.pluginsdir p in
         if verbose () then
           eprintf "[Dynlink] Loading the parser in %S ... with prefix %S@."
             p Config.pluginsdir;
         try
           MyDynlink.loadfile pp;
           if verbose () then  eprintf "Success !@.@."
         with
         | MyDynlink.Error m2 ->
           if not (verbose()) then begin
             eprintf
               "[Dynlink] Loading the parser in plugin %S failed!@." p;
             eprintf ">> Failure message: %s@.@." (MyDynlink.error_message m1);
           end;
           eprintf
             "[Dynlink] Trying to load the plugin from %S failed too!@." pp;
           eprintf ">> Failure message: %s@.@." (MyDynlink.error_message m2);
           exit 1
    )(Options.parsers())
