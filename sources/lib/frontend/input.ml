(******************************************************************************)
(*                                                                            *)
(*     Alt-Ergo: The SMT Solver For Software Verification                     *)
(*     Copyright (C) 2018-2018 --- OCamlPro SAS                               *)
(*                                                                            *)
(*     This file is distributed under the terms of the license indicated      *)
(*     in the file 'License.OCamlPro'. If 'License.OCamlPro' is not           *)
(*     present, please contact us to clarify licensing.                       *)
(*                                                                            *)
(******************************************************************************)

exception Method_not_registered of string

module type S = sig

  (* Parsing *)

  type file

  val parse_file : filename:string -> preludes:string list -> file

  (* Typechecking *)

  type env

  val type_file : file -> (int Typed.atdecl * env) list * env
end

let input_methods = ref []

let register name ((module M : S) as m) =
  input_methods := (name, m) :: !input_methods

let find name =
  try List.assoc name !input_methods
  with Not_found -> raise (Method_not_registered name)

