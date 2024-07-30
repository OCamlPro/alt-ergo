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

(** A wrapper of the Zip module of CamlZip: we use Zip except when we want to
    generate the.js file for try-Alt-Ergo. *)

module ZipWrapper = struct
  include Zip
  let filename e = e.Zip.filename
  let is_directory e = e.Zip.is_directory
end

include ZipWrapper

let extract_zip_file f =
  let cin = open_in f in
  try
    match entries cin with
    | [e] when not @@ is_directory e ->
      if Options.get_verbose () then
        Printer.print_dbg
          ~module_name:"My_zip" ~function_name:"extract_zip_file"
          "I'll read the content of '%s' in the given zip"
          (filename e);
      let content = read_entry cin e in
      close_in cin;
      content
    | _ ->
      close_in cin;
      raise (Arg.Bad
               (Format.sprintf "%s '%s' %s@?"
                  "The zipped file" f
                  "should contain exactly one file."))
  with e ->
    close_in cin;
    raise e

(* !! This commented code is used when compiling to javascript !!
   module DummyZip = struct
   type entry = unit
   type in_file = unit

   let s = "Zip module not available for your setting or has been disabled !"

   let open_in  _  =  failwith s
   let close_in _ = failwith s
   let entries  _  =  failwith s
   let read_entry  _ _  =  failwith s
   let filename  _  =  failwith s
   let is_directory  _  =  failwith s
   end

   include DummyZip
*)
