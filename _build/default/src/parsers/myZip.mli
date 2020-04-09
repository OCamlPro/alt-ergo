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

(** A wrapper of the Zip module of CamlZip: we use Zip except when we want to
    generate the.js file for try-Alt-Ergo **)

type in_file
type entry

val open_in : string -> in_file

val close_in : in_file -> unit

val entries : in_file -> entry list

val read_entry : in_file -> entry -> string

val filename : entry -> string

val is_directory : entry -> bool
