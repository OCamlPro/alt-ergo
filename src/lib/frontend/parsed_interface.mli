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

open Parsed

(** Declaration of types  **)

val mk_abstract_type_decl :
  Loc.t -> string list -> string -> decl
  [@ocaml.ppwarning "TODO: add documentation for every function in this file"]

val mk_enum_type_decl : Loc.t -> string list -> string -> string list -> decl

val mk_algebraic_type_decl :
  Loc.t -> string list -> string ->
  (string * (string * ppure_type) list) list -> decl

val mk_record_type_decl :
  Loc.t -> string list -> string -> ?constr : string ->
  (string * ppure_type) list -> decl

val mk_rec_type_decl : Parsed.type_decl list -> decl

(** Declaration of symbols, functions, predicates, and goals *)

val mk_logic :
  Loc.t -> Symbols.name_kind -> (string * string) list -> plogic_type -> decl

val mk_function_def :
  Loc.t ->
  string * string ->
  (Loc.t * string * ppure_type) list ->
  ppure_type -> lexpr -> decl

val mk_ground_predicate_def :
  Loc.t -> string * string -> lexpr -> decl

val mk_non_ground_predicate_def :
  Loc.t ->
  string * string ->
  (Loc.t * string * ppure_type) list -> lexpr -> decl

val mk_goal : Loc.t -> string -> lexpr -> decl


(** Declaration of theories, generic axioms and rewriting rules **)

val mk_theory : Loc.t -> string -> string -> decl list -> decl

val mk_generic_axiom : Loc.t -> string -> lexpr -> decl

val mk_rewriting : Loc.t -> string -> lexpr list -> decl


(** Declaration of theory axioms and case-splits **)

val mk_theory_axiom : Loc.t -> string -> lexpr -> decl

val mk_theory_case_split : Loc.t -> string -> lexpr -> decl

(** Declaration of stack assertions commands *)

val mk_push : Loc.t -> int -> decl

val mk_pop : Loc.t -> int -> decl

(** Making pure and logic types *)

val int_type : ppure_type

val bool_type : ppure_type

val real_type : ppure_type

val unit_type : ppure_type

val mk_bitv_type : string -> ppure_type

val mk_external_type : Loc.t -> ppure_type list -> string -> ppure_type

val mk_var_type : Loc.t -> string -> ppure_type

val mk_logic_type : ppure_type list -> ppure_type option -> plogic_type


(** Making arithmetic expressions and predicates **)

val mk_int_const  : Loc.t -> string -> lexpr

val mk_real_const : Loc.t -> Num.num -> lexpr

val mk_add : Loc.t -> lexpr -> lexpr -> lexpr

val mk_sub : Loc.t -> lexpr -> lexpr -> lexpr

val mk_mul : Loc.t -> lexpr -> lexpr -> lexpr

val mk_div : Loc.t -> lexpr -> lexpr -> lexpr

val mk_mod : Loc.t -> lexpr -> lexpr -> lexpr

val mk_pow_int : Loc.t -> lexpr -> lexpr -> lexpr

val mk_pow_real : Loc.t -> lexpr -> lexpr -> lexpr

val mk_minus : Loc.t -> lexpr -> lexpr

val mk_pred_lt : Loc.t -> lexpr -> lexpr -> lexpr

val mk_pred_le : Loc.t -> lexpr -> lexpr -> lexpr

val mk_pred_gt : Loc.t -> lexpr -> lexpr -> lexpr

val mk_pred_ge : Loc.t -> lexpr -> lexpr -> lexpr


(** Making Record expressions **)

val mk_record : Loc.t -> (string * lexpr) list -> lexpr

val mk_with_record : Loc.t -> lexpr -> (string * lexpr) list -> lexpr

val mk_dot_record : Loc.t -> lexpr -> string -> lexpr


(** Making Array expressions **)

val mk_array_get : Loc.t -> lexpr -> lexpr -> lexpr

val mk_array_set :
  Loc.t -> lexpr -> lexpr -> lexpr -> lexpr


(** Making Bit-vector expressions **)

val mk_bitv_const : Loc.t -> string -> lexpr

val mk_bitv_extract : Loc.t -> lexpr -> string -> string -> lexpr

val mk_bitv_concat : Loc.t -> lexpr -> lexpr -> lexpr


(** Making Boolean / Propositional expressions **)

val mk_true_const : Loc.t -> lexpr

val mk_false_const : Loc.t -> lexpr

val mk_and : Loc.t -> lexpr -> lexpr -> lexpr

val mk_or : Loc.t -> lexpr -> lexpr -> lexpr

val mk_xor : Loc.t -> lexpr -> lexpr -> lexpr

val mk_iff : Loc.t -> lexpr -> lexpr -> lexpr

val mk_implies : Loc.t -> lexpr -> lexpr -> lexpr

val mk_not : Loc.t -> lexpr -> lexpr

val mk_distinct : Loc.t -> lexpr list -> lexpr

val mk_pred_eq : Loc.t -> lexpr -> lexpr -> lexpr
val mk_pred_not_eq : Loc.t -> lexpr -> lexpr -> lexpr


(** Making quantified formulas **)

val mk_forall :
  Loc.t ->
  (string * string * ppure_type) list ->
  (lexpr list * bool) list ->
  lexpr list -> lexpr -> lexpr

val mk_exists :
  Loc.t ->
  (string * string * ppure_type) list ->
  (lexpr list * bool) list ->
  lexpr list -> lexpr -> lexpr


(** Naming and casting types of expressions **)

val mk_type_cast : Loc.t -> lexpr -> ppure_type -> lexpr

val mk_named : Loc.t -> string -> lexpr -> lexpr


(** Making vars, applications, if-then-else, and let expressions **)

val mk_var : Loc.t -> string -> lexpr

val mk_application : Loc.t -> string -> lexpr list -> lexpr

val mk_pattern : Loc.t -> string -> string list -> pattern

val mk_ite : Loc.t -> lexpr -> lexpr -> lexpr -> lexpr

val mk_let : Loc.t -> (string * lexpr) list -> lexpr -> lexpr

val mk_void : Loc.t -> lexpr


(** Making particular expression used in semantic triggers **)

val mk_in_interval : Loc.t -> lexpr -> bool -> lexpr -> lexpr -> bool -> lexpr

val mk_maps_to : Loc.t -> string -> lexpr -> lexpr


(** Making cuts and checks **)

val mk_check : Loc.t -> lexpr -> lexpr

val mk_cut : Loc.t -> lexpr -> lexpr

val mk_match : Loc.t -> lexpr -> (pattern * lexpr) list -> lexpr

val mk_algebraic_test : Loc.t -> lexpr -> string -> lexpr

val mk_algebraic_project : Loc.t -> guarded:bool -> lexpr -> string -> lexpr
