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
val translate_binop : Why3_ptree.binop -> string
val translate_quant : Why3_ptree.quant -> string
val translate_term : Why3_ptree.term -> string
val translate_theory_decl : Why3_ptree.decl -> string
val str_of_loc : Why3_loc.position -> string
val translate_theory_decl_option :
  Why3_ptree.decl option * Why3_loc.position -> string
val translate_theory_decls : decls -> string
val str_of_lab : Why3_ptree.label -> string
val translate_theory_head : Why3_ptree.ident -> string
val translate_theory : Why3_ptree.ident * decls -> string
val translate : ast -> string
val main : string -> unit
val debug : bool
