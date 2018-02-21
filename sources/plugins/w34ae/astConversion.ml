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

open Parsed
open Parsed_interface

open Why3_ptree
open Why3_number

let get_infix_ident i =
  List.hd (List.rev (String.split_on_char ' ' i.id_str))

let str_of_label = function
  | Lstr l -> l.lab_string
  | _ -> ""

let str_of_labs labs =
  String.concat " " (List.filter (fun x -> x <> "") (List.map str_of_label labs))

let dummy_loc = Why3_loc.dummy_position

(* TRANSLATORS  *)
let translate_quant quant =
    match quant with
    | Tforall -> mk_forall
    | Texists -> mk_exists
    | _ -> Format.eprintf "TODO@."; assert false
    
let translate_binop = function
  | Tand -> mk_and
  | Tor -> mk_or
  | Timplies -> mk_implies
  | Tiff -> mk_iff
  | _ -> Format.eprintf "TODO@."; assert false

let translate_tuple exp_list loc =
  let length = string_of_int (List.length exp_list) in
  let field_name = "Tuple" ^ length ^ "_proj_" in
  let rec trad l n =
    match l with
    | [] -> []
    | h::t ->
       let fn = field_name ^ string_of_int n in
       (fn ,h)::(trad t (n + 1))
  in
  let str_exp_list = trad exp_list 1 in
  mk_record loc str_exp_list


let translate_binder (b : Why3_ptree.binder) : string * string * Parsed.ppure_type  =
  match b with
  | (_, Some i, Some pty) -> (i.id_str, "", pty)
  | _ -> Format.eprintf "TODO@."; assert false

let translate_innfix_ident i loc t1 t2=
  let inf_id_str = get_infix_ident i in
  match inf_id_str with
  | "+" -> mk_add loc t1 t2
  | "-" -> mk_sub  loc t1 t2
  | "*" ->  mk_mul  loc t1 t2
  | "<" -> mk_pred_lt  loc t1 t2
  | "<=" -> mk_pred_le  loc t1 t2
  | ">" -> mk_pred_gt  loc t1 t2
  | ">=" -> mk_pred_gt  loc t1 t2
  | "=" -> mk_pred_eq loc t1 t2
  | "==" -> mk_application loc "infix_eqeq" [t1; t2]
  | "+->" -> mk_application loc "infix_plmngt" [t1; t2]
  | "-->" -> mk_application loc "infix_mnmngt" [t1; t2]
  | "<+" -> mk_application loc "infix_lspl" [t1; t2]
  | "-->>" -> mk_application loc "infix_mnmngtgt" [t1; t2]
  | ">->>" -> mk_application loc "infix_gtmngtgt" [t1; t2]
  | ">->" -> mk_application loc "infix_gtmngt" [t1; t2]
  | _ ->  Format.eprintf "TODO@."; assert false

(* ??? CHECK with infix dans innfix semantic  *)
let translate_infix_ident = translate_innfix_ident

let translate_qualid = function
  | Qident { id_str = "True"; id_loc} -> mk_true_const id_loc
  | Qident { id_str = "False"; id_loc} -> mk_false_const id_loc
  | Qident { id_str; id_loc} -> mk_var id_loc id_str                 
  | Qdot (q, i) -> (* ignore module prefix, functions in prelude *)
     mk_var i.id_loc i.id_str

let translate_apply {pp_loc; pp_desc} tradt1 loc =
  match pp_desc with
  | PPvar "singleton" ->
     let empty = mk_application loc "empty" [] in
     mk_application loc "add" [tradt1; empty]
  | PPvar s ->  mk_application loc s [tradt1]                             
  | PPapp (s, ll) -> mk_application loc s (ll @ [tradt1])                                    
  | _ ->  Format.eprintf "TODO@."; assert false
                                          

let translate_idapp q [le] loc =
  match q  with
  | Qident {id_str = "prefix -"} ->
     mk_minus loc le
  | Qident {id_str = "infix -"} ->
     mk_minus loc le
  | _  -> Format.eprintf "TODO@."; assert false
