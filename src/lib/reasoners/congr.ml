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
module Ex = Explanation
module Sy = Symbols
module X = Shostak.Combine

let src = Logs.Src.create ~doc:"Congr" __MODULE__

module Log = (val Logs.src_log src : Logs.LOG)

module App = struct
  type t = App of Sy.t * X.r list * Ty.t

  module T0 = struct
    type nonrec t = t

    let print ppf (App (f, xs, _ty)) =
      Fmt.pf ppf "%a@[<1>(%a)@]" Sy.print f (Fmt.list ~sep:Fmt.comma X.print) xs

    let equal (App (f1, xs1, ty1)) (App (f2, xs2, ty2)) =
      Sy.equal f1 f2 && List.equal X.equal xs1 xs2 && Ty.equal ty1 ty2

    let hash (App (f, xs, ty)) =
      let open Fasthash in
      init 0
      |> combine_int (Sy.hash f)
      |> combine_list X.hash xs
      |> combine_int (Ty.hash ty)
      |> finalize

    let compare (App (f1, xs1, ty1)) (App (f2, xs2, ty2)) =
      let c = Sy.compare f1 f2 in
      if c <> 0
      then c
      else
        let c = List.compare X.compare xs1 xs2 in
        if c <> 0 then c else Ty.compare ty1 ty2
  end

  include Container_types.Make (T0)

  let from_term uf f xs ty = App (f, List.map (Uf.make uf) xs, ty)

  let args (App (_, rs, _)) = rs

  let canonicalise uf (App (f, rs, ty)) =
    App (f, List.map (fun r -> fst (Uf.find_r uf r)) rs, ty)
end

type r = X.r

type parents =
  { terms : App.t E.Map.t;
    literals : Ex.t E.Map.t
  }

let no_parents = { terms = E.Map.empty; literals = E.Map.empty }

let union_parents { terms = terms1; literals = literals1 }
    { terms = terms2; literals = literals2 } =
  let terms =
    E.Map.union
      (fun _ app1 app2 ->
        Options.heavy_assert (fun () -> App.equal app1 app2);
        Some app1)
      terms1 terms2
  in
  let literals =
    E.Map.union (fun _ ex1 ex2 -> Some (Ex.merge ex1 ex2)) literals1 literals2
  in
  { terms; literals }

type t =
  { current : App.t E.Map.t;
        (** If [current(e)] is [f(rr1, ..., rrn)] then the following holds:

            1. [e] is [f(x1, ..., xn)], with [rri = Uf.find xi], and

            2. [n > 0] (i.e. [e] is not a constant), and

            3. [f] is an uninterpreted function symbol

            Moreover, there is a _unique_ entry in [current] for a given
            congruence class, i.e. there is no other entry [e'] in [current]
            such that [current(e')] is [f(rr1, ..., rrn)]. *)
    root : E.t App.Map.t;
        (** [root] is the inverse of [current]: [root(f(rr1, ..., rrn)) = e] if
            and only if [current(e) = f(rr1, ..., rrn)].

            [root] contains the congruence representative for the congruence
            class [f(rr1, ..., rrn)]. *)
    parents : parents X.Map.t
        (** [parents(r)] contains all the terms [e] such that:

            1. [e] is in [current], and

            2. [e] is [f(x1, ..., xn)], with [r = Uf.make xi] for some [xi]
            (note that this if [Uf.make], not [Uf.find]: [parents] is _not_
            keyed on the canonical representatives)

            {b Note}: each expression in [parents] is associated with its [make]
            application, i.e. if [e] is [f(x1, ..., xn)] it is associated with
            [f(r1, ..., rn)] where each [ri] is [Uf.make xi], avoiding repeated
            lookups into the [make] map. *)
  }

let print ppf t = E.Map.print App.print ppf t.current

let empty =
  { parents = X.Map.empty; root = App.Map.empty; current = E.Map.empty }

let add_to_parents parents rs parent =
  List.fold_left
    (fun parents r ->
      X.Map.update r
        (function
          | None -> Some parent
          | Some old_parents -> Some (union_parents old_parents parent))
        parents)
    parents rs

let add_term_to_parents parents app e =
  add_to_parents parents (App.args app)
    { terms = E.Map.singleton e app; literals = E.Map.empty }

let add_literal_to_parents parents rs a ex =
  add_to_parents parents rs
    { terms = E.Map.empty; literals = E.Map.singleton a ex }

let remove_term_from_parents parents app e =
  let rs = App.args app in
  List.fold_left
    (fun parents r ->
      X.Map.update r
        (function
          | None -> None
          | Some { terms; literals } ->
            let terms = E.Map.remove e terms in
            if E.Map.is_empty terms && E.Map.is_empty literals
            then None
            else Some { terms; literals })
        parents)
    parents rs

let remove_literal_from_parents parents rs a =
  List.fold_left
    (fun parents r ->
      X.Map.update r
        (function
          | None -> None
          | Some { terms; literals } ->
            let literals = E.Map.remove a literals in
            if E.Map.is_empty terms && E.Map.is_empty literals
            then None
            else Some { terms; literals })
        parents)
    parents rs

let update_term t uf app_make e eqs =
  let app_canon = App.canonicalise uf app_make in
  match App.Map.find app_canon t.root with
  | e' when E.equal e e' -> t, eqs
  | e' ->
    let t =
      match E.Map.find e t.current with
      | exception Not_found -> t
      | old_app ->
        (* If [e] was in [current], remove it from all the maps -- it is now
           equal to [e'] by congruence, so we only need to keep track of
           [e']. *)
        let root = App.Map.remove old_app t.root
        and current = E.Map.remove e t.current
        and parents = remove_term_from_parents t.parents app_make e in
        { root; current; parents }
    in
    t, E.Map.add e e' eqs
  | exception Not_found ->
    let root, parents =
      (* If [e] was already in [current], its children are already in [parents]
         and its old inverse needs to be removed, since we are replacing it with
         [app_canon].

         But if [e] was *not* in [current], we need to add its children to
         [parents] for future updates. *)
      match E.Map.find e t.current with
      | exception Not_found -> t.root, add_term_to_parents t.parents app_make e
      | old_app -> App.Map.remove old_app t.root, t.parents
    in
    let root = App.Map.add app_canon e root in
    let current = E.Map.add e app_canon t.current in
    { root; parents; current }, eqs

let add_term t uf e eqs =
  let { E.f; E.xs; E.ty; _ } = E.term_view e in
  if Compat.List.is_empty xs || X.fully_interpreted f
  then t, eqs
  else update_term t uf (App.from_term uf f xs ty) e eqs

(** precondition: [a] is a literal *)
let add_literal t uf a ex =
  let { E.xs; _ } = E.term_view a in
  let rs = List.map (Uf.make uf) xs in
  let parents = add_literal_to_parents t.parents rs a ex in
  { t with parents }

(** precondition: [a] is a literal *)
let remove_literal t uf a =
  let { E.xs; _ } = E.term_view a in
  let rs = List.map (Uf.make uf) xs in
  let parents = remove_literal_from_parents t.parents rs a in
  { t with parents }

let congr_close_up t r up =
  match X.Map.find r t.parents with
  | up' -> union_parents up up'
  | exception Not_found -> up

let up_close_up t uf { terms; literals } =
  let t, eqs =
    E.Map.fold
      (fun e app_make (t, eqs) -> update_term t uf app_make e eqs)
      terms (t, E.Map.empty)
  in
  t, eqs, literals
