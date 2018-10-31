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


val get_current : unit -> (module Sat_solver_sig.SatContainer)
(** returns the current activated SAT-solver depending on the value of
    `Options.sat_solver ()`. See command-line option `-sat-solver` for
    more details **)


(*
(*+ no dynamic loading of SAT solvers anymore +*)
val set_current : (module Sat_solver_sig.S) -> unit
(** sets a new SAT-solver. This function is intended to be used by dynamically
    loaded plugins **)
*)
