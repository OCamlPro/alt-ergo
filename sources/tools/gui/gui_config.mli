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

val window_width : int
val window_height : int
val indent_size : int
val max_indent : int
val max_indents : int
val monospace_font : string
val general_font : string
val style : string
val wrap : bool

(** Load the configuration from default location *)
val load : unit -> unit

(** Write the configuration file to the default location *)
val write : unit -> unit

(** Update the size of the window *)
val update_window_size : int -> int -> unit

(** Update the monospace font *)
val update_monospace_font : string -> unit

val update_wrap : bool -> unit

val not_supported : string -> 'a
