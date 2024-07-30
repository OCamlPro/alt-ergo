(**************************************************************************)
(*                                                                        *)
(*     Alt-Ergo: The SMT Solver For Software Verification                 *)
(*     Copyright (C) --- OCamlPro SAS                                     *)
(*                                                                        *)
(*     This file is distributed under the terms of OCamlPro               *)
(*     Non-Commercial Purpose License, version 1.                         *)
(*                                                                        *)
(*     As an exception, Alt-Ergo Club members at the Gold level can       *)
(*     use this file under the terms of the Apache Software License       *)
(*     version 2.0.                                                       *)
(*                                                                        *)
(*     ---------------------------------------------------------------    *)
(*                                                                        *)
(*     The Alt-Ergo theorem prover                                        *)
(*                                                                        *)
(*     Sylvain Conchon, Evelyne Contejean, Francois Bobot                 *)
(*     Mohamed Iguernelala, Stephane Lescuyer, Alain Mebsout              *)
(*                                                                        *)
(*     CNRS - INRIA - Universite Paris Sud                                *)
(*                                                                        *)
(*     ---------------------------------------------------------------    *)
(*                                                                        *)
(*     More details can be found in the directory licenses/               *)
(*                                                                        *)
(**************************************************************************)

type t = { content : string ; id : int}

module HC =
  Hconsing.Make(struct
    type elt = t
    let hash s = Hashtbl.hash s.content
    let eq s1 s2 = String.equal s1.content s2.content
    let set_id n v = {v with id = n}
    let initial_size = 9001
    let disable_weaks () = Options.get_disable_weaks ()
  end)

let make s = HC.make {content = s; id = - 1}

let view s = s.content

let print fmt v = Format.fprintf fmt "%s" (view v)

let equal s1 s2 = s1.id == s2.id

let compare s1 s2 = compare s1.id s2.id

let hash s = s.id

let empty = make ""

let rec list_assoc x = function
  | [] -> raise Not_found
  | (y, v) :: l -> if equal x y then v else list_assoc x l

let save_cache () =
  HC.save_cache ()

let reinit_cache () =
  HC.reinit_cache ()

module Arg = struct type t'= t type t = t' let compare = compare end
module Set : Set.S with type elt = t = Set.Make(Arg)
module Map : Map.S with type key = t = Map.Make(Arg)
