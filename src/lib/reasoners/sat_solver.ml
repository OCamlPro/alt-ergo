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

let get = function
  | Util.Tableaux | Util.Tableaux_CDCL ->
    if Options.get_verbose () then
      Printer.print_dbg
        ~module_name:"Sat_solver"
        "use Tableaux-like solver";
    (module Fun_sat_frontend : Sat_solver_sig.SatContainer)
  | Util.CDCL | Util.CDCL_Tableaux ->
    if Options.get_verbose () then
      Printer.print_dbg
        ~module_name:"Sat_solver"
        "use CDCL solver";
    (module Satml_frontend : Sat_solver_sig.SatContainer)


let get_current () = get (Options.get_sat_solver ())

let get_theory ~no_th =
  if no_th then
    (module Theory.Main_Empty : Theory.S)
  else
    (module Theory.Main_Default : Theory.S)
