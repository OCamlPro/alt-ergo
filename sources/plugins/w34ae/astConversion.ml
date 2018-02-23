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


let str_of_label = function
  | Lstr l -> l.lab_string
  | _ -> ""

let str_of_labs labs =
  String.concat " " (List.filter (fun x -> x <> "") (List.map str_of_label labs))

let dummy_loc = Why3_loc.dummy_position

(* TRANSLATORS  *)
   

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



let translate_qualid = function
  | Qident { id_str = "True"; id_loc} -> mk_true_const id_loc
  | Qident { id_str = "False"; id_loc} -> mk_false_const id_loc
  | Qident { id_str; id_loc} -> mk_var id_loc id_str                 
  | Qdot (q, i) -> (* ignore module prefix, functions in prelude *)
     mk_var i.id_loc i.id_str 
                                     
