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

  type parsed

  val parse_files :
    filename:string -> preludes:string list -> parsed Seq.t

  (* Typechecking *)

  type env

  val empty_env : env

  val type_parsed : env -> parsed -> int Typed.atdecl list * env

end

let input_methods = ref []

let register name ((module M : S) as m) =
  input_methods := (name, m) :: !input_methods

let find name =
  try List.assoc name !input_methods
  with Not_found -> raise (Method_not_registered name)

