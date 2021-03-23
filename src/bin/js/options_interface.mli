(******************************************************************************)
(*                                                                            *)
(*     Alt-Ergo: The SMT Solver For Software Verification                     *)
(*     Copyright (C) 2018-2020 --- OCamlPro SAS                               *)
(*                                                                            *)
(*     This file is distributed under the terms of the license indicated      *)
(*     in the file 'License.OCamlPro'. If 'License.OCamlPro' is not           *)
(*     present, please contact us to clarify licensing.                       *)
(*                                                                            *)
(******************************************************************************)

(** {1 Options interface module} *)

(** This module aims to set options of the Alt-Ergo's lib that are set in
    the worker_interface options type *)

(** Function use to set Alt-Ergo's options from worker_interface options type *)
val set_options : Worker_interface.options -> unit
