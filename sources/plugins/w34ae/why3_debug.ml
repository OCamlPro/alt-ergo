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

open Why3_ident
open Why3_ptree
open Why3_number
open Why3_decl
       

let print_string s debug =
  let str = if debug then "\n !!! STRING DEBUG : " ^ s ^ "\n"  else "" in
  Format.eprintf "%s" str
       
                        (* Debug - Printers of Why3_ptree*)
       
(* Logical terms and formulas *)

(* From Why3_number  *)
let str_of_constant c =
  let str_of_constI = function
    | IConstDec s -> "IConstDec : " ^  s
    | IConstHex s -> "IConstHex : " ^  s
    | IConstOct s -> "IConstOct : " ^  s
    | IConstBin s -> "IConstBin : " ^  s in
  let str_of_constR r =
     Format.eprintf "TODO@."; assert false in
  match c with
  | ConstInt i -> str_of_constI i
  | ConstReal r -> str_of_constR r

let print_constant c debug =
  let str = if debug then (str_of_constant c) else "" in
  Format.eprintf "%s" str


(* label *)
let str_of_label = function
  | Lstr l -> l.lab_string
  | _ -> ""

let str_of_labs labs =
  String.concat " " (List.filter (fun x -> x <> "") (List.map str_of_label labs))

                
(* binop  *)
let str_of_binop bo = function
  | Tand -> "Tand"
  | Tand_asym -> "Tand_asym"
  | Tor -> "Tor"
  | Tor_asym -> "Tor_asym"
  | Timplies -> "Timplies"
  | Tiff -> "Tiff"
  | Tby -> "Tby"
  | Tso -> "Tso"

             
(* unop  *)
let str_of_unop = function
  | Tnot -> "Tnot"

              
(* bool *)
let str_of_bool b = if b then "true" else "false"

                                            
(* ident *)
let str_of_ident i =
  "ident : {id_str = " ^ i.id_str ^ "; id_lab = " ^ str_of_labs i.id_lab ^ "}"

let print_ident i debug =
  let str = if debug then (str_of_ident i) else "" in
  Format.eprintf "%s" str

                 
(* infix *)
let get_infix_ident i =
  List.hd (List.rev (String.split_on_char ' ' i.id_str))

let print_infix i debug =
  let str = if debug then "{infix : " ^ (get_infix_ident i) ^ "}" else "" in
  Format.eprintf "%s" str

                 
(* qualid  *)
let rec str_of_qualid = function
  | Qident i -> "qualid (Qident) : " ^ (str_of_ident i)
  | Qdot (q, i) -> "qualid (Qdot) : (" ^ (str_of_qualid q) ^ ", " ^  (str_of_ident i) ^ ")"

let print_qualid q debug =
  let str = if debug then (str_of_qualid q) else "" in
    Format.eprintf "%s" str

                   
(* pty  *)
let rec str_of_pty =
let str_of_pty_list pl =
  "[" ^ (String.concat "; " (List.map str_of_pty pl)) ^ "]" in
  function
  | PTtyvar (i, op) -> "pty (PTtyvar) : (" ^ (str_of_ident i) ^ ", " ^  (str_of_bool op) ^ ")"
  | PTtyapp (q, pl) -> "pty (PTtyapp) : (" ^ str_of_qualid q ^ ", " ^
                         str_of_pty_list pl ^ ")"
  | PTtuple pl -> "pty (PTtuple) : " ^ str_of_pty_list pl
  | PTarrow (p0 , p1) -> "pty (PTarrow) : (" ^ str_of_pty p0 ^ ", " ^  str_of_pty p1 ^ ")"
  | PTparen p -> "pty (PTparen) : " ^ str_of_pty p

let print_pty pty debug =
  let str = if debug then "pty : " ^ (str_of_pty pty) else "" in
  Format.eprintf "%s" str

                 
(* binder  *)
let str_of_binder (_, op_i, _, op_pty) =
  let str_i =
    match op_i with
    | None -> "None"
    | Some i -> str_of_ident i in
  let str_pty =
    match op_pty with
    | None -> "None"
    | Some pty -> str_of_pty pty in
  "binder : (_, " ^ str_i ^ ", _," ^ str_pty ^ ")"
                   
let print_binder b debug =
     let str = if debug then str_of_binder b else "" in
     Format.eprintf "%s" str

                    
(* param  *)
let str_of_param (_, op_i, _, pty) =
    let str_i =
    match op_i with
    | None -> "None"
    | Some i -> str_of_ident i in
    "param : (_, " ^ str_i ^ ", _," ^ str_of_pty pty ^ ")"

let print_param p debug =
     let str = if debug then str_of_param p else "" in
     Format.eprintf "%s" str                                                        

                    
(* pattern  
let str_of_pattern (pat_desc; _) =
  "pattern : "*)
                    
(* TODO ? : pat_desc *)



(* Why3_declarations. *)

(* field  *)
let str_of_field {f_loc; f_ident; f_pty; f_mutable
                  ; f_ghost} =
  "field : {" ^ str_of_ident f_ident ^ "; " ^ str_of_pty f_pty
  ^ "; _; _}"

let print_field f debug =
  let str = if debug then str_of_field f else "" in
  Format.eprintf "%s" str

(* type_def *)
let str_of_type_def = function
  | TDabstract -> "type_def (TDabstract)"
  | TDalias pty -> "type_def (TDalias) : " ^ str_of_pty pty 
  | TDalgebraic l ->
     let str_of_param_list pl =
       "[" ^ (String.concat "; " (List.map str_of_param pl)) ^ "]" in
     let str_al (_, i, pl ) = "(_, " ^ str_of_ident i
                              ^ ", " ^ str_of_param_list pl ^ ")" in
     "type_def (TDalgebraic) : [" ^(String.concat ";"
      (List.map str_al l) ) ^ "]"                                                       
  | TDrecord fl -> "type_def (TDrecord) : ["
                ^ (String.concat "; " (List.map str_of_field fl))
  | TDrange (x, y) -> "type_def (TDrange) : TODO"
  | TDfloat (x,y) -> "type_def (TDfloat) : TODO"                       

let print_type_def td debug =
  let str = if debug then str_of_type_def td else "" in
  Format.eprintf "%s" str                                        

(* term *)
let rec str_of_term {term_desc; term_loc} =
  let str_of_term_list l =
    "[" ^ (String.concat "; " (List.map str_of_term l))  ^ "]" in
  match term_desc with
  | Ttrue -> "term (Ttrue)"
  | Tfalse -> "term (Tfalse)"
  | Tconst c -> "term (Tconst) : " ^ str_of_constant c
  | Tident q -> "term (Tident) : " ^ str_of_qualid q
  | Tidapp (q, tl) ->
     "term (Tidapp) : (" ^ str_of_qualid q ^ ", " ^ str_of_term_list tl ^ ")"
  | Tapply (t0, t1) ->
     "term (Tapply) : (" ^ str_of_term t0 ^ ", " ^ str_of_term t1 ^ ")"
  | Tinfix (t0, i, t1) ->
     "term (Tinfix) : (" ^  str_of_term t0 ^ ", " ^ str_of_ident i
     ^ ", " ^ str_of_term t1 ^ ")"
  | Tinnfix (t0, i, t1) ->
     "term (Tinnfix) : (" ^  str_of_term t0 ^", " ^ str_of_ident i
     ^ ", " ^ str_of_term t1 ^ ")"
  | Tbinop (t0, bo, t1) ->
     "term (Tbinop) : (" ^ str_of_term t0 ^ ", " ^ str_of_binop bo bo
     ^ ", " ^ str_of_term t1 ^ ")"
  | Tunop (uo, t) ->
     "term (Tunop) : (" ^ str_of_unop uo ^ ", " ^ str_of_term t ^ ")"
  | Tif(t0, t1, t2) ->
     "term (Tif) : (" ^ str_of_term t0 ^ ", " ^ str_of_term t1 ^ ", "
     ^ str_of_term t2 ^ ")"
  | Tquant (q, bl, tll, t) ->
     "term Tquant : TODO" (*of quant * binder list * term list list * term*)
  | Tnamed (l, t) ->
     "term (Tnamed) : (" ^  str_of_label l ^ ", " ^str_of_term t ^ ")"
  | Tlet (i, t0, t1) ->
     "term (Tlet) : (" ^ str_of_ident i ^ ", " ^ str_of_term t0 ^ ", "
     ^ str_of_term t1 ^ ")"
  | Tmatch (t, l) -> "term (Tmatch) : TODO "
  | Tcast (t, pty) -> "term (Tcast) : TODO" 
  | Ttuple l -> "term (Ttuple) : TODO"
  | Trecord l -> "term (Trecord) : TODO"
  | Tupdate (t, l) -> "term Tupdate : TODO"

let print_term t debug =
  let str = if debug then str_of_term t else "" in
  Format.eprintf "%s" str
  
                 
(* invariant  *)
let str_of_invariant i = 
"invariant : [" ^ (String.concat "; " (List.map str_of_term i)) ^ "]"
                 
(* type_decl  *)
let str_of_type_decl
      {td_loc; td_ident; td_params; td_model; td_vis; td_def; td_inv}
  =
  let str_of_ident_list p = "" in
  "type_decl : {td_loc; " ^ str_of_ident td_ident ^ "; " ^ str_of_ident_list td_params
  ^ "; td_model; td_vis; " ^ str_of_type_def td_def
  ^ "; " ^ str_of_invariant td_inv ^ "}"
                    
let print_type_decl tyd debug =
  let str = if debug then str_of_type_decl tyd else "" in
  Format.eprintf "%s" str

(* logic_decl  *)
let str_of_logic_decl
      {ld_loc; ld_ident; ld_params; ld_type; ld_def} =
  let str_of_param_list pl =
    "[" ^ (String.concat "; " (List.map str_of_param ld_params)) ^ "]"
  in
  let str_of_pty_option = function
    | None -> "Notype"
    | Some pty -> str_of_pty pty in
  let str_of_term_option = function
    | None -> "_"
    | Some t -> str_of_term t in
  "logic_decl : {_" ^  str_of_ident ld_ident ^ "; " ^
    str_of_param_list ld_params ^ "; " ^ str_of_pty_option ld_type
    ^ "; " ^ str_of_term_option ld_def ^ "}"

let print_logic_decl ld debug =
  let str = if debug then str_of_logic_decl ld else "" in
  Format.eprintf "%s" str

let str_of_decl d =
  let str_of_logic_decl_list ldl =
     "[" ^ (String.concat "; " (List.map str_of_logic_decl ldl)) ^ "]"
  in
  let str_of_type_decl_list tdl =
     "[" ^ (String.concat "; " (List.map str_of_type_decl tdl)) ^ "]"
  in
  match d with 
  | Dtype tdl -> "decl (Dtype) : " ^ str_of_type_decl_list tdl
  | Dlogic ldl  -> "decl (Dlogic) : " ^ str_of_logic_decl_list ldl
  | Dind (_, _) -> Format.eprintf "TODO@."; assert false
  | Dprop (pk, i, t) ->
     let str_of_prop_kind =
       (function
        | Plemma -> "Plemma"
        | Paxiom -> "Paxiom"
        | Pgoal -> "Pgoal"
        | Pskip -> "Pskip")
     in
     "decl (Dprop) : (" ^ str_of_prop_kind pk ^ ", " ^ str_of_ident i
     ^ ", " ^ str_of_term t
  | Dmeta (_, _) -> Format.eprintf "TODO@."; assert false

let print_decl d debug =
  let str = if debug then str_of_decl d else "" in
  Format.eprintf "%s" str

let rec str_of_theory_decls dcls acc =
    match dcls with
    | [] -> acc
    | (None, _)::t -> str_of_theory_decls t acc
    | (Some d,_)::t ->  str_of_theory_decls t (acc ^ "; "  ^ str_of_decl d)


let print_theory t debug =
  let str =
    if debug then  "[" ^ str_of_theory_decls t "" ^ "]" else "" in
  Format.eprintf "%s" str
                                               
(* program files *)     
