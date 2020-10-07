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

let get_current () =
  match Options.get_sat_solver () with
  | Util.Tableaux | Util.Tableaux_CDCL ->
    if Options.get_verbose () then
      Printer.print_dbg
        ~module_name:"Sat_solver"
        "use Tableaux-like solver";
    (module Fun_sat : Sat_solver_sig.SatContainer)
  | Util.CDCL | Util.CDCL_Tableaux ->
    if Options.get_verbose () then
      Printer.print_dbg
        ~module_name:"Sat_solver"
        "use CDCL solver";
    (module Satml_frontend : Sat_solver_sig.SatContainer)
