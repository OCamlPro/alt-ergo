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

module E = Expr

type rootdep = { name : string; f : Expr.t; loc : Loc.t}

type exp =
  | Literal of Satml_types.Atom.atom
  | Fresh of int
  | Bj of E.t
  | Dep of E.t
  | RootDep of rootdep

module S =
  Set.Make
    (struct
      type t = exp
      let compare a b = match a,b with
        | Fresh i1, Fresh i2 -> i1 - i2
        | Literal a  , Literal b   -> Satml_types.Atom.cmp_atom a b
        | Dep e1  , Dep e2   -> E.compare e1 e2
        | RootDep r1, RootDep r2 -> E.compare r1.f r2.f
        | Bj e1   , Bj e2    -> E.compare e1 e2

        | Literal _, _ -> -1
        | _, Literal _ -> 1

        | Fresh _, _ -> -1
        | _, Fresh _ -> 1

        | Dep _, _ -> 1
        | _, Dep _ -> -1
        | RootDep _, _ -> 1
        | _, RootDep _ -> -1

    end)

let is_empty t = S.is_empty t

type t = S.t

exception Inconsistent of t * Expr.Set.t list

let empty = S.empty

let union s1 s2 =
  if s1 == s2 then s1 else S.union s1 s2

let singleton e = S.singleton e

let mem e s = S.mem e s

let remove e s =
  if S.mem e s then S.remove e s
  else raise Not_found

let iter_atoms f s = S.iter f s

let fold_atoms f s acc = S.fold f s acc

(* TODO : XXX : We have to choose the smallest ??? *)
let merge s1 _s2 = s1

let fresh_exp =
  let r = ref (-1) in
  fun () ->
    incr r;
    Fresh !r

let exists_fresh t =
  S.exists (function
      | Fresh _ -> true
      | _ -> false
    ) t

let remove_fresh fe s =
  if S.mem fe s then Some (S.remove fe s)
  else None

let add_fresh fe s = S.add fe s

let print fmt ex =
  let open Format in
  if Options.get_debug_explanations () then begin
    fprintf fmt "{";
    S.iter (function
        | Literal a -> fprintf fmt "{Literal:%a}, " Satml_types.Atom.pr_atom a
        | Fresh i -> fprintf fmt "{Fresh:%i}" i;
        | Dep f -> fprintf fmt "{Dep:%a}" E.print f
        | RootDep r -> fprintf fmt "{RootDep:%s}" r.name
        | Bj f -> fprintf fmt "{BJ:%a}" E.print f
      ) ex;
    fprintf fmt "}"
  end

let get_unsat_core dep =
  fold_atoms
    (fun a acc ->
       match a with
       | RootDep r -> r :: acc
       | Dep _ -> acc
       | Bj _ | Fresh _ | Literal _ -> assert false
    ) dep []

let print_unsat_core ?(tab=false) fmt dep =
  iter_atoms
    (function
      | RootDep r ->
        if tab then Format.fprintf fmt "  %s@." r.name (* tab is too big *)
        else Format.fprintf fmt "%s@." r.name
      | Dep _ -> ()
      | Bj _ | Fresh _ | Literal _ -> assert false
    ) dep

let formulas_of s =
  S.fold (fun e acc ->
      match e with
      | Dep f | Bj f -> E.Set.add f acc
      | RootDep _ | Fresh _ -> acc
      | Literal _ -> assert false (*TODO*)
    ) s E.Set.empty

let bj_formulas_of s =
  S.fold (fun e acc ->
      match e with
      | Bj f -> E.Set.add f acc
      | Dep _ | RootDep _ | Fresh _ -> acc
      | Literal _ -> assert false (*TODO*)
    ) s E.Set.empty

module MI = Util.MI

let make_deps sf =
  E.Set.fold (fun l acc -> S.add (Bj l) acc) sf S.empty

let has_no_bj s =
  try S.iter (function Bj _ -> raise Exit | _ -> ())s; true
  with Exit -> false

let compare = S.compare

let subset = S.subset
