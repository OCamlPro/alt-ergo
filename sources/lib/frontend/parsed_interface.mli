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

open Parsed

(** Declaration of types  **)

val mk_abstract_type_decl : Loc.t -> string list -> string -> decl
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
