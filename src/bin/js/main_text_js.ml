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

open Alt_ergo_common

(* Register input method and parsers *)
let register_input () =
  Input_frontend.register_legacy ()

(* done here to initialize options,
   before the instantiations of functors *)
let parse_cmdline () =
  try Parse_command.parse_cmdline_arguments ()
  with Parse_command.Exit_parse_command i -> exit i

let () =
  register_input ();
  parse_cmdline ();
  Signals_profiling.init_signals ();
  Solving_loop.main ()
