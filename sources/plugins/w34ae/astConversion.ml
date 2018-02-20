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

type decls = (Why3_ptree.decl option * Why3_loc.position) list
type theory = (Why3_ptree.ident * decls )
type ast = theory list

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

let rec translate_pty =
  let translate_pty_list l = List.map translate_pty l in
  function
  | PTtyapp (Qident {id_str = "int"}, _) -> int_type
  | PTtyapp (Qident {id_str = "bool"}, _) -> bool_type
  | PTtyapp (Qident {id_str = "real"}, _) -> real_type
  | PTtyapp (Qident {id_str; id_loc}, pl) ->
     mk_external_type id_loc (List.map translate_pty pl) id_str
  | PTtuple pl ->
     let length =  string_of_int (List.length pl) in
     let name = "tuple" ^ length in
     let loc = dummy_loc in
     let ptyl = translate_pty_list pl in
     mk_external_type loc ptyl name
  | PTparen pty  -> translate_pty pty
  | _ ->  Format.eprintf "TODO@."; assert false                     


let translate_binder (b : Why3_ptree.binder) : string * string * Parsed.ppure_type  =
  match b with
  | (_, Some i, false, Some pty) -> (i.id_str, "", translate_pty pty)
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

let rec translate_term (t : Why3_ptree.term) : Parsed.lexpr  =
  let loc =  t.term_loc in
  let translate_term_list tl = List.map translate_term tl in
  match t.term_desc with
  | Ttrue -> mk_true_const loc
  | Tfalse -> mk_false_const loc
  | Tconst (ConstInt (IConstDec s)) -> mk_int_const loc s                         
  | Tconst c -> Format.eprintf "TODO@."; assert false
  | Tident q -> translate_qualid q  
  | Tidapp (q, tl) -> translate_idapp q (translate_term_list tl) loc
  | Tapply ({term_desc = Tapply ({term_desc = Tident (Qident {id_str = "mod"})}, t0)},t1) ->
     mk_application loc "comp_mod" [(translate_term t0); (translate_term t1)]
  | Tapply ({term_desc = Tapply ({term_desc = Tident (Qident {id_str = "div"})}, t0)},t1) ->
     mk_application loc "comp_div" [(translate_term t0); (translate_term t1)]
  | Tapply ({term_desc = Tapply ({term_desc = Tident (Qident {id_str = "domain_restriction"})}, t0)},t1) ->
     mk_application loc "infix_lsbr" [(translate_term t0); (translate_term t1)]
  | Tapply ({term_desc = Tapply ({term_desc = Tident (Qident {id_str = "domain_substraction"})}, t0)},t1) ->
     mk_application loc "infix_lslsbr" [(translate_term t0); (translate_term t1)]
  | Tapply ({term_desc = Tapply ({term_desc = Tident (Qident {id_str = "range_substraction"})}, t0)},t1) ->
     mk_application loc "infix_brgtgt" [(translate_term t0); (translate_term t1)]
| Tapply ({term_desc = Tapply ({term_desc = Tident (Qident {id_str = "range_restriction"})}, t0)},t1) ->
     mk_application loc "infix_brgt" [(translate_term t0); (translate_term t1)]
  | Tapply (t0, t1) ->
       translate_apply (translate_term t0) (translate_term t1) loc
  | Tinfix (tl, i, tr) -> (* ??? TO CHECK  *)
     translate_infix_ident i loc (translate_term tl) (translate_term tr)
  | Tinnfix (tl, i, tr) ->
       translate_innfix_ident i loc (translate_term tl)
         (translate_term tr)
  | Tbinop (tl, bo, tr) ->
     translate_binop bo loc (translate_term tl) (translate_term tr) 
  | Tunop (u, t) -> mk_not loc (translate_term t)
  | Tif (t0, t1, t2) ->
     mk_ite loc (translate_term t0) (translate_term t1) (translate_term t2)
  | Tquant (quant, binder_list, term_list_list, term) ->
     let vs_ty = List.map translate_binder binder_list in
     let triggers =
       List.map (fun tl -> ((translate_term_list tl), true))
         term_list_list in
     let filters = [] in (* ??? FIX OR NOT  ???  *)
     translate_quant quant loc vs_ty triggers filters (translate_term term)
  | Tnamed (lab, t) -> mk_named loc (str_of_label lab) (translate_term t)
  | Tlet (id, t0, t1) -> mk_let loc id.id_str (translate_term t0) (translate_term t1)
  | Tmatch (_, _) -> Format.eprintf "TODO@."; assert false
  | Tcast (t, pty) -> mk_type_cast loc (translate_term t) (translate_pty pty)
  | Ttuple tl -> translate_tuple (translate_term_list tl) loc
  | Trecord _ -> Format.eprintf "TODO@."; assert false
  | Tupdate (_, _) -> Format.eprintf "TODO@."; assert false



let translate_logic_aux ld_params ld_type named_ident loc  =
       let ppure_type_list =
         List.map (fun (_, _, pty) -> pty ) ld_params
       in
       let ppure_type_option =
         match ld_type with
         | None -> None
         | Some pty -> Some (translate_pty pty)
       in
       let logic_type =
         mk_logic_type ppure_type_list ppure_type_option in
       let name_k = Symbols.Other in
       (*!!! TODO/CHECK : ss_list is always a singleton ???*)
       let ss_list = [named_ident] in
       mk_logic loc name_k ss_list logic_type
                                                 
