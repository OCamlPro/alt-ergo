(******************************************************************************)
(*                                                                            *)
(*  Alt-Ergo: The SMT Solver For Software Verification                        *)
(*  Copyright (C) --- OCamlPro SAS                                            *)
(*                                                                            *)
(*  This software is governed by the CeCILL  license under French law and     *)
(*  abiding by the rules of distribution of free software.  You can  use,     *)
(*  modify and/ or redistribute the software under the terms of the CeCILL    *)
(*  license as circulated by CEA, CNRS and INRIA at the following URL         *)
(*  "http://www.cecill.info".                                                 *)
(*                                                                            *)
(*  As a counterpart to the access to the source code and  rights to copy,    *)
(*  modify and redistribute granted by the license, users are provided only   *)
(*  with a limited warranty  and the software's author,  the holder of the    *)
(*  economic rights,  and the successive licensors  have only  limited        *)
(*  liability.                                                                *)
(*                                                                            *)
(*  In this respect, the user's attention is drawn to the risks associated    *)
(*  with loading,  using,  modifying and/or developing or reproducing the     *)
(*  software by the user in light of its specific status of free software,    *)
(*  that may mean  that it is complicated to manipulate,  and  that  also     *)
(*  therefore means  that it is reserved for developers  and  experienced     *)
(*  professionals having in-depth computer knowledge. Users are therefore     *)
(*  encouraged to load and test the software's suitability as regards their   *)
(*  requirements in conditions enabling the security of their systems and/or  *)
(*  data to be ensured and,  more generally, to use and operate it in the     *)
(*  same conditions as regards security.                                      *)
(*                                                                            *)
(*  The fact that you are presently reading this means that you have had      *)
(*  knowledge of the CeCILL license and that you accept its terms.            *)
(*                                                                            *)
(*  ------------------------------------------------------------------------  *)
(*                                                                            *)
(*  This is a free release of Alt-Ergo under the terms of CeCILL license.     *)
(*  The latest releases of Alt-Ergo are distributed under the terms of        *)
(*  OCamlPro Non-Commercial Purpose License, version 1.                       *)
(*                                                                            *)
(*  ------------------------------------------------------------------------  *)
(*                                                                            *)
(*  The Alt-Ergo theorem prover                                               *)
(*                                                                            *)
(*  Sylvain Conchon, Evelyne Contejean, Francois Bobot                        *)
(*  Mohamed Iguernelala, Stephane Lescuyer, Alain Mebsout                     *)
(*                                                                            *)
(*  CNRS - INRIA - Universite Paris Sud                                       *)
(*                                                                            *)
(*  ------------------------------------------------------------------------  *)
(*                                                                            *)
(*  More details can be found in the directory licenses/                      *)
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
