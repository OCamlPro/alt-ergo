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

exception Method_not_registered of string

module type S = sig

  (* Parsing *)

  type parsed

  val parse_file : content:string -> format:string option -> parsed Seq.t

  val parse_files :
    filename:string -> preludes:string list -> parsed Seq.t

  (* Typechecking *)

  type env

  val empty_env : env

  val type_parsed :
    env -> env Stack.t -> parsed -> int Typed.atdecl list * env

end

let input_methods = ref []

let register name ((module M : S) as m) =
  input_methods := (name, m) :: !input_methods

let find name =
  try List.assoc name !input_methods
  with Not_found -> raise (Method_not_registered name)
