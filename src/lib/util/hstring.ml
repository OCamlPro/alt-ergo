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

open Options

type t = { content : string ; id : int}

module S =
  Hconsing.Make(struct
    type elt = t
    let hash s = Hashtbl.hash s.content
    let eq s1 s2 = String.equal s1.content s2.content
    let set_id n v = {v with id = n}
    let initial_size = 9001
    let disable_weaks () = Options.get_disable_weaks ()
  end)

let make s = S.make {content = s; id = - 1}

let view s = s.content

let print fmt v = Format.fprintf fmt "%s" (view v)

let equal s1 s2 = s1.id == s2.id

let compare s1 s2 = compare s1.id s2.id

let hash s = s.id

let empty = make ""

let rec list_assoc x = function
  | [] -> raise Not_found
  | (y, v) :: l -> if equal x y then v else list_assoc x l

let fresh_string =
  let cpt = ref 0 in
  fun () ->
    incr cpt;
    "!k" ^ (string_of_int !cpt)

let is_fresh_string s =
  try s.[0] == '!' && s.[1] == 'k'
  with Invalid_argument s ->
    assert (String.compare s "index out of bounds" = 0);
    false

let is_fresh_skolem s =
  try s.[0] == '!' && s.[1] == '?'
  with Invalid_argument s ->
    assert (String.compare s "index out of bounds" = 0);
    false

module Arg = struct type t'= t type t = t' let compare = compare end
module Set : Set.S with type elt = t = Set.Make(Arg)
module Map : Map.S with type key = t = Map.Make(Arg)
