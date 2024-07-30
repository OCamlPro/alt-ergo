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

let plugins_locations = AltErgoSites.Sites.plugins

let preludes_locations = AltErgoSites.Sites.preludes

(* {!List.find_map} from OCaml >= 4.10 *)
let rec find_map f = function
  | [] -> None
  | x :: xs ->
    match f x with
    | Some _ as y -> y
    | None -> find_map f xs

let lookup_file locations filename =
  find_map
    (fun location ->
       let filename = Filename.concat location filename in
       if Sys.file_exists filename then Some filename else None)
    locations

let lookup_prelude = lookup_file preludes_locations

let lookup_plugin = lookup_file plugins_locations

let load_plugin plugin =
  try
    AltErgoSites.Plugins.Plugins.load plugin
  with e ->
    AltErgoLib.Errors.run_error
      (Dynlink_error
         (Format.asprintf
            "@[<v>Loading the plugin %S failed!@,\
             >> Failure message: %s"
            plugin (Printexc.to_string e)))
