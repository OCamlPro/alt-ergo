(******************************************************************************)
(*                                                                            *)
(*     The Alt-Ergo theorem prover                                            *)
(*     Copyright (C) 2006-2013                                                *)
(*                                                                            *)
(*     Sylvain Conchon                                                        *)
(*     Evelyne Contejean                                                      *)
(*                                                                            *)
(*     Francois Bobot                                                         *)
(*     Mohamed Iguernelala                                                    *)
(*     Stephane Lescuyer                                                      *)
(*     Alain Mebsout                                                          *)
(*                                                                            *)
(*     CNRS - INRIA - Universite Paris Sud                                    *)
(*                                                                            *)
(*     This file is distributed under the terms of the Apache Software        *)
(*     License version 2.0                                                    *)
(*                                                                            *)
(*  ------------------------------------------------------------------------  *)
(*                                                                            *)
(*     Alt-Ergo: The SMT Solver For Software Verification                     *)
(*     Copyright (C) 2013-2018 --- OCamlPro SAS                               *)
(*                                                                            *)
(*     This file is distributed under the terms of the Apache Software        *)
(*     License version 2.0                                                    *)
(*                                                                            *)
(******************************************************************************)

open Format
open Options

module E = Expr

type exp =
  | Literal of Satml_types.Atom.atom
  | Fresh of int
  | Bj of E.t
  | Dep of E.t
  | RootDep of string (* name of the toplevel formula *)

module S =
  Set.Make
    (struct
      type t = exp
      let compare a b = match a,b with
        | Fresh i1, Fresh i2 -> i1 - i2
        | Literal a  , Literal b   -> Satml_types.Atom.cmp_atom a b
        | Dep e1  , Dep e2   -> E.compare e1 e2
        | RootDep s, RootDep t -> String.compare s t
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

let remove_fresh fe s =
  if S.mem fe s then Some (S.remove fe s)
  else None

let add_fresh fe s = S.add fe s

let print fmt ex =
  if Options.debug_explanations () then begin
    fprintf fmt "{";
    S.iter (function
        | Literal a -> fprintf fmt "{Literal:%a}, " Satml_types.Atom.pr_atom a
        | Fresh i -> Format.fprintf fmt "{Fresh:%i}" i;
        | Dep f -> Format.fprintf fmt "{Dep:%a}" E.print f
        | RootDep s -> Format.fprintf fmt "{RootDep:%s}" s
        | Bj f -> Format.fprintf fmt "{BJ:%a}" E.print f
      ) ex;
    fprintf fmt "}"
  end

let print_unsat_core ?(tab=false) fmt dep =
  iter_atoms
    (function
      | RootDep s ->
        if tab then Format.fprintf fmt "  %s@." s (* tab is too big *)
        else Format.fprintf fmt "%s@." s
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

let rec literals_of_acc lit fs f acc = match E.form_view f with
  | E.Not_a_form -> assert false
  | E.Literal _ ->
    if lit then f :: acc else acc
  | E.Iff(f1, f2) ->
    let g = E.elim_iff f1 f2 (E.id f) ~with_conj:true in
    literals_of_acc lit fs g acc
  | E.Xor(f1, f2) ->
    let g = E.neg @@ E.elim_iff f1 f2 (E.id f) ~with_conj:false in
    literals_of_acc lit fs g acc
  | E.Unit (f1,f2) ->
    let acc = literals_of_acc false fs f1 acc in
    literals_of_acc false fs f2 acc
  | E.Clause (f1, f2, _) ->
    let acc = literals_of_acc true fs f1 acc in
    literals_of_acc true fs f2 acc
  | E.Lemma _ ->
    acc
  | E.Skolem { E.main = f; _ } ->
    literals_of_acc true fs f acc
  | E.Let { E.in_e; let_e; _ } ->
    literals_of_acc true fs in_e @@ literals_of_acc true fs let_e acc

let literals_of ex =
  let fs  = formulas_of ex in
  E.Set.fold (literals_of_acc true fs) fs []

module MI = Map.Make (struct type t = int let compare = compare end)

let literals_ids_of ex =
  List.fold_left (fun acc f ->
      let i = E.id f in
      let m = try MI.find i acc with Not_found -> 0 in
      MI.add i (m + 1) acc
    ) MI.empty (literals_of ex)


let make_deps sf =
  E.Set.fold (fun l acc -> S.add (Bj l) acc) sf S.empty

let has_no_bj s =
  try S.iter (function Bj _ -> raise Exit | _ -> ())s; true
  with Exit -> false

let compare = S.compare

let subset = S.subset
