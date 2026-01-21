(*********************************************************************************)
(*                                                                               *)
(*     Alt-Ergo: The SMT Solver For Software Verification                        *)
(*     Copyright (C) --- OCamlPro SAS                                            *)
(*                                                                               *)
(*     This software is governed by the CeCILL  license under French law and     *)
(*     abiding by the rules of distribution of free software.  You can  use,     *)
(*     modify and/ or redistribute the software under the terms of the CeCILL    *)
(*     license as circulated by CEA, CNRS and INRIA at the following URL         *)
(*     "http://www.cecill.info".                                                 *)
(*                                                                               *)
(*     As a counterpart to the access to the source code and  rights to copy,    *)
(*     modify and redistribute granted by the license, users are provided only   *)
(*     with a limited warranty  and the software's author,  the holder of the    *)
(*     economic rights,  and the successive licensors  have only  limited        *)
(*     liability.                                                                *)
(*                                                                               *)
(*     In this respect, the user's attention is drawn to the risks associated    *)
(*     with loading,  using,  modifying and/or developing or reproducing the     *)
(*     software by the user in light of its specific status of free software,    *)
(*     that may mean  that it is complicated to manipulate,  and  that  also     *)
(*     therefore means  that it is reserved for developers  and  experienced     *)
(*     professionals having in-depth computer knowledge. Users are therefore     *)
(*     encouraged to load and test the software's suitability as regards their   *)
(*     requirements in conditions enabling the security of their systems and/or  *)
(*     data to be ensured and,  more generally, to use and operate it in the     *)
(*     same conditions as regards security.                                      *)
(*                                                                               *)
(*     The fact that you are presently reading this means that you have had      *)
(*     knowledge of the CeCILL license and that you accept its terms.            *)
(*                                                                               *)
(*     ------------------------------------------------------------------------  *)
(*                                                                               *)
(*     This is a free release of Alt-Ergo under the terms of CeCILL license.     *)
(*     The latest releases of Alt-Ergo are distributed under the terms of        *)
(*     OCamlPro Non-Commercial Purpose License, version 1.                       *)
(*                                                                               *)
(*     As an exception, Alt-Ergo Club members at the Gold level can              *)
(*     use this file under the terms of the Apache Software License              *)
(*     version 2.0.                                                              *)
(*                                                                               *)
(*     ------------------------------------------------------------------------  *)
(*                                                                               *)
(*     The Alt-Ergo theorem prover                                               *)
(*                                                                               *)
(*     Sylvain Conchon, Evelyne Contejean, Francois Bobot                        *)
(*     Mohamed Iguernelala, Stephane Lescuyer, Alain Mebsout                     *)
(*                                                                               *)
(*     CNRS - INRIA - Universite Paris Sud                                       *)
(*                                                                               *)
(*     ------------------------------------------------------------------------  *)
(*                                                                               *)
(*     More details can be found in the directory licenses/                      *)
(*                                                                               *)
(*********************************************************************************)

open AltErgoLib
open Options

type action =
  | Prune of int
  | IncorrectPrune of int
  | Unprune of int
  | AddInstance of int * string * string list
  | AddTrigger of int * bool * string
  | LimitLemma of int * string * int
  | UnlimitLemma of int * string

let resulting_ids = Hashtbl.create 17

let save actions ac =
  (* (match ac with *)
  (*   | Prune id -> *)
  (*       Printer.print_dbg "Prune %d" id *)
  (*   | IncorrectPrune id -> *)
  (*       Printer.print_dbg "Incorrectprune %d" id *)
  (*   | Unprune id -> *)
  (*       Printer.print_dbg "Unrune %d" id *)
  (*   | AddInstance (id, name, vars) -> *)
  (*       Printer.print_dbg "AddInstance %d %s" id name *)
  (*   | AddTrigger (id, inst_buf, trs) -> *)
  (*       Printer.print_dbg "AddTriger %d %b %s" id inst_buf trs *)
  (*   | LimitLemma (id, name, nb) -> *)
  (*       Printer.print_dbg "LimitLemma %d-%s %d" id name nb *)
  (* ); *)
  Stack.push ac actions

let compute_ids_offsets old_res res =
  List.fold_left (fun acc (name1, id1) ->
      try let id2 = List.assoc name1 res in
        (* if id1 = id2 then acc else *) (id1, id2 - id1)::acc
      with Not_found -> acc) [] old_res

let offset_id id offsets =
  let nid = ref id in
  try
    List.iter
      (fun (i, off) ->
         if id <= i then (nid := id + off; raise Exit))
      offsets;
    id
  with Exit -> !nid


let offset_stack st offsets =
  let l = ref [] in
  while not (Stack.is_empty st) do
    let ac = match Stack.pop st with
      | Prune id -> Prune (offset_id id offsets)
      | IncorrectPrune id -> IncorrectPrune (offset_id id offsets)
      | Unprune id -> Unprune (offset_id id offsets)
      | AddInstance (id, name, vars) ->
        AddInstance ((offset_id id offsets), name, vars)
      | AddTrigger (id, inst_buf, trs) ->
        AddTrigger ((offset_id id offsets), inst_buf, trs)
      | LimitLemma (id, name, nb) ->
        LimitLemma ((offset_id id offsets), name, nb)
      | UnlimitLemma (id, name) ->
        UnlimitLemma ((offset_id id offsets), name)
    in
    l := ac :: !l
  done;
  List.iter (fun ac -> Stack.push ac st) !l

let read_actions res = function
  | Some cin ->
    begin
      try
        let old_res = (input_value cin: (string * int) list) in
        let st = (input_value cin: action Stack.t) in
        let offsets = compute_ids_offsets old_res res in
        offset_stack st offsets;
        st
      with End_of_file -> Stack.create ()
    end
  | None -> Stack.create ()


module SI = Util.SI

let safe_session actions =
  let l = ref [] in
  Stack.iter (fun a -> l := a::!l) actions;
  let list_actions = !l in
  let _, incorrect_prunes =
    List.fold_left (fun (prunes, incorrect_prunes) -> function
        | Prune id -> SI.add id prunes, incorrect_prunes
        | IncorrectPrune id -> prunes, SI.add id incorrect_prunes
        | Unprune id -> SI.remove id prunes, SI.remove id incorrect_prunes
        | _ -> prunes, incorrect_prunes)
      (SI.empty, SI.empty) list_actions
  in
  SI.is_empty incorrect_prunes
