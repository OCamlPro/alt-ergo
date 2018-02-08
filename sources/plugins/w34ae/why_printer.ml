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

open Lexing
open Parsed
       

(*TODO/FIXME symetric to AstConvertion.w32aeloc*)
let str_of_loc (ll, rl) =
  let str_of_lex_pos
    {
      pos_fname = pf;
      pos_lnum = pl;
      pos_bol = pb;
      pos_cnum = pc
    }
    = "{pos_fname = " ^ pf ^ "; pos_lnum = " ^ (string_of_int pl) ^
        "; pos_bol = " ^ (string_of_int pb) ^ "; pos_cnum = " ^
          (string_of_int pc) ^ "}" in
  str_of_lex_pos ll

let loc_comment l = "(* " ^ (str_of_loc l) ^ " *)"

let rec str_of_ppure_type pp  =
  let str_of_ppure_type_list l =
    "[" ^ (String.concat "; " (List.map str_of_ppure_type l)) ^ "]" in
         match pp with
  | PPTint -> "PPTint"
  | PPTbool -> "PPTbool"
  | PPTreal -> "PPTreal"
  | PPTunit -> "PPTunit"
  | PPTbitv i -> "PPTbitv " ^ string_of_int i
  | PPTvarid (s, _) -> "PPTvarid " ^ s
  | PPTexternal (l, s, _) ->
     "PPTexternal : (" ^ str_of_ppure_type_list l ^ ", " ^ s ^ ")"

let str_of_pp_infix  = function
  | PPand -> "PPand"
  | PPor -> "PPor"
  | PPimplies -> "PPimplies"
  | PPiff -> "PPiff"
  | PPlt -> "PPlt"
  | PPle -> "PPle"
  | PPgt -> "PPgt"
  | PPge -> "PPge"
  | PPeq -> "PPeq"
  | PPneq -> "PPneq"
  | PPadd -> "PPadd"
  | PPsub -> "PPsub"
  | PPmul -> "PPmul"
  | PPdiv -> "PPdiv"
  | PPmod -> "PPmod"

let str_of_constant = function
  | ConstBitv s -> "ConstBitv : " ^ s
  | ConstInt s -> "ConstInt : " ^ s
  | ConstReal n -> "ConstReal : TODO"
  | ConstTrue -> "ConstTrue"
  | ConstFalse -> "ConstFalse"
  | ConstVoid -> "ConstVoid"

let rec str_of_lexpr {pp_loc; pp_desc} =
  let str_of_lexpr_list l =
    "[" ^ (String.concat "; " (List.map str_of_lexpr l)) ^ "]"
  in
  let str_of_PP_quant_n sspl llbl ll le =
    let str_of_llb (ll, _) = str_of_lexpr_list ll in
    let str_of_ssp (s0, s1, ppt) =
      "(" ^ s0 ^ ", " ^ s1 ^ ", " ^ str_of_ppure_type ppt  ^ ")" in
    "(" ^
    "[" ^ (String.concat "; " (List.map str_of_ssp sspl))  ^ "]" ^
    "[" ^ (String.concat "; " (List.map str_of_llb llbl) ) ^ "], " ^
    str_of_lexpr_list ll ^ ", " ^ str_of_lexpr le ^ ")"
  in
  match pp_desc with
  | PPvar s -> "PPvar : " ^ s
  | PPapp (s, lel) -> "PPapp : (" ^ s ^ ", " ^ str_of_lexpr_list lel ^
  ")"
  | PPmapsTo (s, le) -> Format.eprintf "TODO@."; assert false
  | PPinInterval (_,_,_,_,_) -> Format.eprintf "TODO@."; assert false
  | PPdistinct lel -> Format.eprintf "TODO@."; assert false
  | PPconst c -> "PPconst : " ^ str_of_constant c
  | PPinfix (le, ppi, le2) ->
     "PPinfix : (" ^  str_of_lexpr le ^ ", " ^ str_of_pp_infix ppi ^ ", " ^
       str_of_lexpr le2 ^ ")"
  | PPprefix (pp, le) -> Format.eprintf "TODO@."; assert false
  | PPget (le, le2) -> Format.eprintf "TODO@."; assert false
  | PPset (le, le2, le3) -> Format.eprintf "TODO@."; assert false
  | PPdot (le, s) -> Format.eprintf "TODO@."; assert false
  | PPrecord l -> Format.eprintf "TODO@."; assert false
  | PPwith (le, slel) -> Format.eprintf "TODO@."; assert false
  | PPextract (le,le2,le3) -> Format.eprintf "TODO@."; assert false
  | PPconcat (le, le2) -> Format.eprintf "TODO@."; assert false
  | PPif (le, le2, le3) -> Format.eprintf "TODO@."; assert false
  | PPforall (_,_,_,_) -> Format.eprintf "TODO@."; assert false
  | PPexists (_,_,_,_) -> Format.eprintf "TODO@."; assert false
  | PPforall_named  (sspl, llbl, ll, le) -> "forall : " ^ str_of_PP_quant_n sspl llbl ll le
  | PPexists_named  (_,_,_,_) -> Format.eprintf "TODO@."; assert false
  | PPnamed (_,_) ->  Format.eprintf "TODO@."; assert false
  | PPlet (_,_,_) ->  Format.eprintf "TODO@."; assert false
  | PPcheck le ->  Format.eprintf "TODO@."; assert false
  | PPcut le ->  Format.eprintf "TODO@."; assert false
  | PPcast (_,_) ->  Format.eprintf "TODO@."; assert false

let print_lexpr le debug =
    let str = if debug then (str_of_lexpr le) else "" in
  Format.eprintf "%s" str
                                                     

let str_of_Parsed_decl (pd : Parsed.decl)  =
  match pd with
  | Theory (_, _, _, _) -> Format.eprintf "TODO@."; assert false
  | Axiom (_, _, _, _) -> Format.eprintf "TODO@."; assert false
  | Rewriting (_, _, _) -> Format.eprintf "TODO@."; assert false
  | Goal (l, s, le) -> "Goal : (_, " ^ s ^ ", " ^ str_of_lexpr le ^ ")"
  | Logic (_, _, _, _) -> Format.eprintf "TODO@."; assert false
  | Predicate_def (_, _, _, _) -> Format.eprintf "TODO@."; assert false
  | Function_def (_, _, _, _, _) -> Format.eprintf "TODO@."; assert false
  | TypeDecl (_, _, _, _) -> Format.eprintf "TODO@."; assert false

let rec str_of_why_ast (ast : Parsed.decl list)  =
  match ast with
  | [] -> ""
  | h::t -> (str_of_Parsed_decl h) ^ str_of_why_ast t

let print_why_ast trad =
  let str_header =
    "\n******************** Alt-Ergo langage traduction ****************\n\n" in 
  let str_footer =
    "\n\n*****************************************************************\n" in
  let str_of_trad = str_of_why_ast trad in
  let str = str_header ^ str_of_trad ^ str_footer in
  print_string (str)

let main trad =
  print_why_ast trad; trad
