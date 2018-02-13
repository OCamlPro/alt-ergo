(*******************************************************************************)
(*                                                                             *)
(*   W34AE: A parser of Why3 logic for Alt-Ergo                                *)
(*                                                                             *)
(*   Copyright 2011-2017 OCamlPro SAS                                          *)
(*                                                                             *)
(*   All rights reserved.  This file is distributed under the terms of         *)
(*   the GNU Lesser General Public License version 2.1, with the               *)
(*   special exception on linking described in the file LICENSE.               *)
(*                                                                             *)
(*******************************************************************************)

type decls = (Why3_ptree.decl option * Why3_loc.position) list
type theory = Why3_ptree.ident * decls
type ast = theory list

val dummy_loc : Loc.t
val translate_quant :
  Why3_ptree.quant ->
  Loc.t ->
  (string * string * Parsed.ppure_type) list ->
  (Parsed.lexpr list * bool) list ->
  Parsed.lexpr list -> Parsed.lexpr -> Parsed.lexpr
val translate_binop :
  Why3_ptree.binop -> Loc.t -> Parsed.lexpr -> Parsed.lexpr -> Parsed.lexpr
val translate_tuple : Parsed.lexpr list -> Loc.t -> Parsed.lexpr
val translate_pty : Why3_ptree.pty -> Parsed.ppure_type
val translate_binder :
  Why3_ptree.binder -> string * string * Parsed.ppure_type
val translate_innfix_ident :
  Why3_ptree.ident -> Loc.t -> Parsed.lexpr -> Parsed.lexpr -> Parsed.lexpr
val translate_infix_ident :
  Why3_ptree.ident -> Loc.t -> Parsed.lexpr -> Parsed.lexpr -> Parsed.lexpr
val translate_const_int : Why3_number.integer_constant -> string
val translate_const : Why3_ptree.constant -> Loc.t -> Parsed.lexpr
val translate_qualid : Why3_ptree.qualid -> Parsed.lexpr
val translate_apply : Parsed.lexpr -> Parsed.lexpr -> Loc.t -> Parsed.lexpr
val translate_idapp :
  Why3_ptree.qualid -> Parsed.lexpr list -> Loc.t -> Parsed.lexpr
val translate_unop : Why3_ptree.unop -> Loc.t -> Parsed.lexpr -> Parsed.lexpr
val translate_term : Why3_ptree.term -> Parsed.lexpr
val translate_param :
  Why3_loc.position * Why3_ptree.ident option * 'a * Why3_ptree.pty ->
  Loc.t * string * Parsed.ppure_type
val translate_type_decl : Why3_ptree.type_decl -> Parsed.decl
val translate_pty2 :
  Why3_ptree.pty -> (Loc.t * string * Parsed.ppure_type) list
val translate_logic_decl : Why3_ptree.logic_decl -> Parsed.decl
