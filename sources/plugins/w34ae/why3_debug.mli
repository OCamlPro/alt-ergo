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

val print_string : string -> bool -> unit
val str_of_constant : Why3_number.constant -> string
val print_constant : Why3_number.constant -> bool -> unit
val str_of_label : Why3_ptree.label -> string
val str_of_labs : Why3_ptree.label list -> string
val str_of_binop : 'a -> Why3_ptree.binop -> string
val str_of_unop : Why3_ptree.unop -> string
val str_of_bool : bool -> string
val str_of_ident : Why3_ptree.ident -> string
val print_ident : Why3_ptree.ident -> bool -> unit
val get_infix_ident : Why3_ptree.ident -> string
val print_infix : Why3_ptree.ident -> bool -> unit
val str_of_qualid : Why3_ptree.qualid -> string
val print_qualid : Why3_ptree.qualid -> bool -> unit
val str_of_pty : Why3_ptree.pty -> string
val print_pty : Why3_ptree.pty -> bool -> unit
val str_of_binder :
  'a * Why3_ptree.ident option * 'b * Why3_ptree.pty option -> string
val print_binder :
  'a * Why3_ptree.ident option * 'b * Why3_ptree.pty option -> bool -> unit
val str_of_param :
  'a * Why3_ptree.ident option * 'b * Why3_ptree.pty -> string
val print_param :
  'a * Why3_ptree.ident option * 'b * Why3_ptree.pty -> bool -> unit
val str_of_field : Why3_ptree.field -> string
val print_field : Why3_ptree.field -> bool -> unit
val str_of_type_def : Why3_ptree.type_def -> string
val print_type_def : Why3_ptree.type_def -> bool -> unit
val str_of_term : Why3_ptree.term -> string
val print_term : Why3_ptree.term -> bool -> unit
val str_of_invariant : Why3_ptree.term list -> string
val str_of_type_decl : Why3_ptree.type_decl -> string
val print_type_decl : Why3_ptree.type_decl -> bool -> unit
val str_of_logic_decl : Why3_ptree.logic_decl -> string
val print_logic_decl : Why3_ptree.logic_decl -> bool -> unit
val str_of_decl : Why3_ptree.decl -> string
val print_decl : Why3_ptree.decl -> bool -> unit
val str_of_theory_decls :
  (Why3_ptree.decl option * 'a) list -> string -> string
val print_theory : (Why3_ptree.decl option * 'a) list -> bool -> unit
