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

val get_current : unit -> (module Sat_solver_sig.S)
(** returns the current activated SAT-solver. The default value is Fun_sat.
    When the selected SAT-solver is an external plugin, the first call of this
    function will attemp to dynamically load it **)

val set_current : (module Sat_solver_sig.S) -> unit
(** sets a new SAT-solver. This function is intended to be used by dynamically
    loaded plugins **)
