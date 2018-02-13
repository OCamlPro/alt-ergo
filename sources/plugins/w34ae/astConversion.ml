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
    | Tlambda -> Format.eprintf "TODO@."; assert false
    
let translate_binop = function
  | Tand -> mk_and
  | Tand_asym -> Format.eprintf "TODO@."; assert false
  | Tor -> mk_or
  | Tor_asym -> Format.eprintf "TODO@."; assert false
  | Timplies -> mk_implies
  | Tiff -> mk_iff
  | Tby -> Format.eprintf "TODO@."; assert false
  | Tso -> Format.eprintf "TODO@."; assert false

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
  | PTtyvar (i, _) -> Format.eprintf "TODO@."; assert false
  | PTtyapp (q, pl) ->
     begin
       match q with
       | Qident i ->
	  begin (* ??? Add any other type ???  *)
	    match i.id_str with
	    | "int" -> int_type
            | "bool" -> bool_type
            | "real" -> real_type
            | "set" ->
               let l = List.map translate_pty pl in
               mk_external_type ( i.id_loc) l i.id_str
            | _ ->
               let l = List.map translate_pty pl in
               mk_external_type ( i.id_loc) l i.id_str
	  end
       | _ -> Format.eprintf "TODO@."; assert false
     end
  | PTtuple pl ->
     let length =  string_of_int (List.length pl) in
     let name = "tuple" ^ length in
     let loc = dummy_loc in
     let ptyl = translate_pty_list pl in
     mk_external_type loc ptyl name
  | PTarrow (p0, p1) ->  Format.eprintf "TODO@."; assert false
  | PTparen pty  -> translate_pty pty

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

let translate_const_int = function
  | IConstDec s -> s
  | IConstHex s -> Format.eprintf "TODO@."; assert false
  | IConstOct s -> Format.eprintf "TODO@."; assert false
  | IConstBin s -> Format.eprintf "TODO@."; assert false

(* Warning Why3_number.constant and Parsed.constant share constructors  *)
let translate_const (c : Why3_ptree.constant) loc : Parsed.lexpr =
  match c with
  | ConstInt i -> mk_int_const loc (translate_const_int i)
  | ConstReal r -> Format.eprintf "TODO@."; assert false

let translate_qualid = function
  | Qident i ->
     let loc =  i.id_loc in
     begin
       match i.id_str with
       | "True" -> mk_true_const loc
       | "False" -> mk_false_const loc
       | _ -> mk_var loc i.id_str
     end
  | Qdot (q, i) -> (* ignore module prefix, functions in prelude *)
     let loc =  i.id_loc in
     mk_var loc i.id_str

let translate_apply {pp_loc; pp_desc} tradt1 loc =
    match pp_desc with
    | PPvar s ->
       begin
         match s with
         | "singleton" ->
            let empty = mk_application loc "empty" [] in
            mk_application loc "add" [tradt1; empty]
         | _ -> mk_application loc s [tradt1]
       end
    | PPapp (s, ll) -> mk_application loc s (ll @ [tradt1])
    | _ ->  Format.eprintf "TODO@."; assert false

let translate_idapp q tradtl loc =
  match q with
  | Qdot (q, i) -> Format.eprintf "TODO@."; assert false
  | Qident i ->
     match get_infix_ident i with
     | "-" ->
        begin
          match tradtl with
          | [le] -> mk_minus loc le
          | _ -> Format.eprintf "TODO@."; assert false
        end
     | _ -> Format.eprintf "TODO@."; assert false

let translate_unop = function
  | Tnot -> mk_not


let rec translate_term (t : Why3_ptree.term) : Parsed.lexpr  =
  let loc =  t.term_loc in
  let translate_term_list tl = List.map translate_term tl in
  match t.term_desc with
  | Ttrue -> mk_true_const loc
  | Tfalse -> mk_false_const loc
  | Tconst c -> translate_const c loc
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
  | Tunop (u, t) -> (translate_unop u) loc (translate_term t)
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

let translate_param (loc, id_op, _, pty) =
  match id_op with
  | None -> Format.eprintf "TODO@."; assert false
  | Some id -> ( loc, id.id_str, translate_pty pty)

let translate_type_decl
      {td_loc; td_ident; td_params; td_model; td_vis; td_def; td_inv}
  =  
  let loc =  td_loc in
  let ty_vars = List.map (fun i -> i.id_str) td_params in
  match td_def with
  | TDabstract -> mk_abstract_type_decl loc ty_vars td_ident.id_str
  | TDalias pty -> Format.eprintf "TODO@."; assert false
  | TDalgebraic l  ->
     let ls = List.map (fun (_, i, _) -> i.id_str) l in
     mk_enum_type_decl loc ty_vars td_ident.id_str ls
  | TDrecord fl  -> Format.eprintf "TODO@."; assert false
  | TDrange (bi0, bi1) -> Format.eprintf "TODO@."; assert false
  | TDfloat (i1, i2) -> Format.eprintf "TODO@."; assert false

let translate_pty2 = function
  | PTtyvar (i, _) -> Format.eprintf "TODO@."; assert false
  | PTtyapp (q, pl) ->
     begin
       match q with
       | Qident i ->
          let loc =  i.id_loc in
          let ppure_t =
            match i.id_str with
            | "int" -> int_type
            | "bool" -> bool_type
	    | _ -> Format.eprintf "TODO@."; assert false in
          [(loc, i.id_str,  ppure_t)] (* !!! TODO/CHECK : recursive
                                 * function + accumulator ??? *)
       | _ -> Format.eprintf "TODO@."; assert false
     end
  | PTtuple pl ->  Format.eprintf "TODO@."; assert false
  | PTarrow (p0, p1) ->  Format.eprintf "TODO@."; assert false
  | PTparen p  ->Format.eprintf "TODO@."; assert false


let translate_logic_decl
      {ld_loc; ld_ident; ld_params; ld_type; ld_def} : Parsed.decl =
  let loc =   ld_loc in
  let named_ident =
    (ld_ident.id_str, str_of_labs ld_ident.id_lab) in
  match ld_def with
  | None ->
     begin
       let ppure_type_list =
         List.map (fun (_, _, _, pty) -> translate_pty pty ) ld_params
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
     end
  | Some t ->
     let expr = translate_term t in
     match ld_type with
     | None ->
        begin
          match ld_params with
          | [] ->  mk_ground_predicate_def loc named_ident expr
          | _ ->
             let args = List.map translate_param ld_params in
             mk_non_ground_predicate_def loc named_ident args expr
        end
     | Some pty ->
        let spp_list = translate_pty2 pty in
        let ppure_t = translate_pty pty in
        mk_function_def loc named_ident spp_list ppure_t expr
