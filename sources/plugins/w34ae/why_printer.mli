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

val str_of_loc : Lexing.position * 'a -> string
val loc_comment : Lexing.position * 'a -> string
val str_of_ppure_type : Parsed.ppure_type -> string
val str_of_pp_infix : Parsed.pp_infix -> string
val str_of_constant : Parsed.constant -> string
val str_of_lexpr : Parsed.lexpr -> string
val print_lexpr : Parsed.lexpr -> bool -> unit
val str_of_Parsed_decl : Parsed.decl -> string
val str_of_why_ast : Parsed.decl list -> string
val print_why_ast : Parsed.decl list -> unit
val main : Parsed.decl list -> Parsed.decl list
