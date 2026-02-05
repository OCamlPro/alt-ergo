(******************************************************************************)
(*                                                                            *)
(*  Alt-Ergo: The SMT Solver For Software Verification                        *)
(*  Copyright (C) --- OCamlPro SAS                                            *)
(*                                                                            *)
(*  This software is governed by the CeCILL  license under French law and     *)
(*  abiding by the rules of distribution of free software.  You can  use,     *)
(*  modify and/ or redistribute the software under the terms of the CeCILL    *)
(*  license as circulated by CEA, CNRS and INRIA at the following URL         *)
(*  "http://www.cecill.info".                                                 *)
(*                                                                            *)
(*  As a counterpart to the access to the source code and  rights to copy,    *)
(*  modify and redistribute granted by the license, users are provided only   *)
(*  with a limited warranty  and the software's author,  the holder of the    *)
(*  economic rights,  and the successive licensors  have only  limited        *)
(*  liability.                                                                *)
(*                                                                            *)
(*  In this respect, the user's attention is drawn to the risks associated    *)
(*  with loading,  using,  modifying and/or developing or reproducing the     *)
(*  software by the user in light of its specific status of free software,    *)
(*  that may mean  that it is complicated to manipulate,  and  that  also     *)
(*  therefore means  that it is reserved for developers  and  experienced     *)
(*  professionals having in-depth computer knowledge. Users are therefore     *)
(*  encouraged to load and test the software's suitability as regards their   *)
(*  requirements in conditions enabling the security of their systems and/or  *)
(*  data to be ensured and,  more generally, to use and operate it in the     *)
(*  same conditions as regards security.                                      *)
(*                                                                            *)
(*  The fact that you are presently reading this means that you have had      *)
(*  knowledge of the CeCILL license and that you accept its terms.            *)
(*                                                                            *)
(*  ------------------------------------------------------------------------  *)
(*                                                                            *)
(*  This is a free release of Alt-Ergo under the terms of CeCILL license.     *)
(*  The latest releases of Alt-Ergo are distributed under the terms of        *)
(*  OCamlPro Non-Commercial Purpose License, version 1.                       *)
(*                                                                            *)
(*  ------------------------------------------------------------------------  *)
(*                                                                            *)
(*  The Alt-Ergo theorem prover                                               *)
(*                                                                            *)
(*  Sylvain Conchon, Evelyne Contejean, Francois Bobot                        *)
(*  Mohamed Iguernelala, Stephane Lescuyer, Alain Mebsout                     *)
(*                                                                            *)
(*  CNRS - INRIA - Universite Paris Sud                                       *)
(*                                                                            *)
(*  ------------------------------------------------------------------------  *)
(*                                                                            *)
(*  More details can be found in the directory licenses/                      *)
(*                                                                            *)
(******************************************************************************)

type env
(** The type of global environment of the typechecker. *)

val empty_env : env
(** The empty/initial environment *)

val type_expr :
  env -> (Symbols.t * Ty.t) list -> Parsed.lexpr -> int Typed.atterm
(** Typecheck an input expression (i.e. term (or formula ?)), given
    a local environment and a list of local types used to extend the
    initial environment.
    @raise Typing_error {!Errors.Typing_error} *)
(* TODO: give the env a proper module with binding functions,
         so that the list argument can be ommitted ? *)

val type_parsed :
  env -> env Stack.t -> Parsed.decl -> int Typed.atdecl list * env
(** Type a single declaration.
    @raise Typing_error {!Errors.Typing_error} *)

val type_file : Parsed.file -> (int Typed.atdecl * env) list * env
(** Type an input file. Returns the successive global environments
    obtained after typing each declaration.
    @raise Typing_error {!Errors.Typing_error} *)


(* TODO: move these functions out of the typechecker *)
(* used by main_gui *)
val split_goals :
  (int Typed.atdecl * 'a) list ->
  ((int Typed.atdecl * 'a) list * string) list

(* exported for compat with lib_usage.ml *)
val split_goals_and_cnf :
  (int Typed.atdecl * 'a) list ->
  (Commands.sat_tdecl list * string) list

