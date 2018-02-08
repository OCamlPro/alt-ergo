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

open Why3_ptree
open Why3_ident

type decls = (Why3_ptree.decl option * Why3_loc.position) list

type theory = (Why3_ptree.ident * decls )

type ast = theory list


let translate_binop bo =
  match bo with
  | Tand -> "/\\"
  | Tand_asym -> "&&"
  | Tor -> "\\/"
  | Tor_asym -> "||"
  | Timplies -> "->"
  | Tiff -> "<->"
  | Tby -> "by"
  | Tso -> "so"

let translate_quant q =
    match q with
    | Tforall -> "forall"
    | Texists -> "exists"
    | Tlambda -> "Tlambda"

let rec translate_term { term_desc = td; _} =
  match td with
  | Ttrue -> "true"
  | Tfalse -> "false"
  | Tconst _ -> "Tconst"
  | Tident _ -> "Tident"
  | Tidapp (_, _) -> "Tidapp"
  | Tapply (_, _) -> "Tapply"
  | Tinfix (_, _, _) -> "Tinfix"
  | Tinnfix (_, _, _) -> "Tinnfix"
  | Tbinop (tl, bo, tr) -> "(" ^ translate_term tl ^ ") " ^ translate_binop bo ^ " (" ^ translate_term tr ^ ")"
  | Tunop (_, _) -> "Tunop"
  | Tif (_, _, _) -> "Tif"
  | Tquant (quant, binder_list, term_list_list, term) -> translate_quant quant ^ " " ^ "Tquant"
  | Tnamed (_, _) -> "Tnamed"
  | Tlet (_, _, _) -> "Tlet"
  | Tmatch (_, _) -> "Tmatch"
  | Tcast (_, _) -> "Tcast"
  | Ttuple _ -> "Ttuple"
  | Trecord _ -> "Trecord"
  | Tupdate (_, _) -> "Tupdate" 

let translate_theory_decl d =
match d with
| Dprop (Why3_decl.Pgoal,  {id_str = istr; id_lab = _; id_loc = _}, term) -> "  goal " ^ istr ^ " : " ^ translate_term term ^ "\n"  
| _ -> "decls\n"

let str_of_loc l =
    match Why3_loc.get l with
    | (fname,lnum,cnum1,cnum2) -> "(* Why3_location | " ^ fname ^ "line " ^ string_of_int lnum ^ ", columns " ^ string_of_int cnum1 ^ ", to " ^ string_of_int cnum2 ^ "*)\n"

let translate_theory_decl_option op =
match op with
| (None, l) -> ""
| (Some d, l) -> str_of_loc l ^ translate_theory_decl d

let translate_theory_decls (dcls : decls) =
  String.concat "" (List.map translate_theory_decl_option dcls)

let str_of_lab l = 
match l with
| Lstr {lab_string=str; lab_tag = _} -> str 
| _ -> ""

let translate_theory_head (id : Why3_ptree.ident) = 
match id with
| {id_str = istr; id_lab = ilab; id_loc = iloc} -> 
  let str_of_ptree_lab_list l = String.concat "" (List.map str_of_lab l) in
  let theo_label = str_of_ptree_lab_list ilab in
  if theo_label = "" then istr ^ "\n"
  else istr ^ " \"" ^ theo_label ^ "\"\n"

let translate_theory (id, decls)  = "\ntheory " ^ (translate_theory_head id) ^ (translate_theory_decls decls) ^ "end\n\n"

let translate (f : ast) = String.concat "" (List.map translate_theory f)

let main filename =
    let cin = open_in filename in
    let lexbuf = Lexing.from_channel cin in
    let f :  (Why3_ptree.ident * (Why3_ptree.decl option * Why3_loc.position) list) list = Why3_parser.logic_file Why3_lexer.token lexbuf in
    let transl = translate f in
    print_string transl

let debug = false

let () = if debug then main Sys.argv.(1) else ()
