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
  let p = Option.value ~default:p (Config.lookup_plugin p) in
  if verbose then
    Printer.print_dbg ~flushed:false ~module_name:"Dynlink"
      "Loading the %s in %S ..." msg p;
  try
    loadfile p;
    if verbose then
      Printer.print_dbg ~header:false
        "Success!"
  with
  | Error m ->
    Errors.run_error
      (Dynlink_error
         (Format.asprintf
            "@[<v>Loading the %s plugin in %S failed!@,\
             >> Failure message: %s"
            msg p (error_message m)))
