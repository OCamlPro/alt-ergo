(******************************************************************************)
(*                                                                            *)
(*     The Alt-Ergo theorem prover                                            *)
(*     Copyright (C) 2006-2013                                                *)
(*                                                                            *)
(*     Sylvain Conchon                                                        *)
(*     Evelyne Contejean                                                      *)
(*                                                                            *)
(*     Francois Bobot                                                         *)
(*     Mohamed Iguernelala                                                    *)
(*     Stephane Lescuyer                                                      *)
(*     Alain Mebsout                                                          *)
(*                                                                            *)
(*     CNRS - INRIA - Universite Paris Sud                                    *)
(*                                                                            *)
(*     This file is distributed under the terms of the Apache Software        *)
(*     License version 2.0                                                    *)
(*                                                                            *)
(*  ------------------------------------------------------------------------  *)
(*                                                                            *)
(*     Alt-Ergo: The SMT Solver For Software Verification                     *)
(*     Copyright (C) 2013-2018 --- OCamlPro SAS                               *)
(*                                                                            *)
(*     This file is distributed under the terms of the Apache Software        *)
(*     License version 2.0                                                    *)
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
  AltErgoLib.Printer.init_colors ();
  AltErgoLib.Printer.init_output_format ();
  Signals_profiling.init_signals ();
  Solving_loop.main ()
