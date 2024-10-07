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

[@@@ocaml.warning "-32-33"]
(** A wrapper of the Zip module of CamlZip *)

let src = Logs.Src.create ~doc:"My_zip" __MODULE__
module Log = (val Logs.src_log src : Logs.LOG)

open Zip

let filename e = e.Zip.filename
let is_directory e = e.Zip.is_directory

let extract_zip_file f =
  if Stdlib.(Sys.backend_type = Bytecode) then
    Errors.unsupported_feature "Zip format in javascript mode";

  let cin = open_in f in
  Fun.protect ~finally:(fun () -> close_in cin) @@ fun () ->
  match entries cin with
  | [e] when not @@ is_directory e ->
    if Options.get_verbose () then
      Log.debug
        (fun k -> k "Extract the content of '%s' in the given zip"
            (filename e));
    read_entry cin e
  | _ ->
    Errors.run_error (Invalid_zip f)

include Zip
