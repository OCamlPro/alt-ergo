(**************************************************************************)
(*                                                                        *)
(*     Alt-Ergo: The SMT Solver For Software Verification                 *)
(*     Copyright (C) 2013-2023 --- OCamlPro SAS                           *)
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
(*     Until 2013, some parts of this code were released under            *)
(*     the Apache Software License version 2.0.                           *)
(*                                                                        *)
(*     ---------------------------------------------------------------    *)
(*                                                                        *)
(*     More details can be found in the directory licenses/               *)
(*                                                                        *)
(**************************************************************************)

open AltErgoLib

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

let load verbose p msg =
  if verbose then
    Printer.print_dbg ~flushed:false ~module_name:"Dynlink"
      "Loading the %s in %S ..." msg p;
  try
    loadfile p;
    if verbose then
      Printer.print_dbg ~header:false
        "Success!"
  with
  | Error m1 ->
    if verbose then begin
      Printer.print_dbg ~header:false
        "@, Loading the %s in plugin %S failed!"
        msg p;
      Printer.print_err
        ">> Failure message: %s" (error_message m1);
    end;
    let pp = Format.sprintf "%s/%s" Config.pluginsdir p in
    if verbose then
      Printer.print_dbg  ~flushed:false ~module_name:"Dynlink"
        "Loading the %s in %S... with prefix %S..."
        msg p Config.pluginsdir;
    try
      loadfile pp;
      if verbose then
        Printer.print_dbg ~header:false
          "Success!"
    with
    | Error m2 ->
      if not (verbose) then begin
        Printer.print_err
          "@, Loading the %s in plugin %S failed!@,\
           >> Failure message: %s"
          msg p
          (error_message m1);
      end;
      Errors.run_error
        (Dynlink_error
           (Format.sprintf
              "@[<v 0>Trying to load the plugin from %S failed too!@ \
               >> Failure message: %s@]" pp (error_message m2)))
