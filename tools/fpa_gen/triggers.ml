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
(*     More details can be found in the directory licenses/               *)
(*                                                                        *)
(**************************************************************************)

module DE = Dolmen.Std.Expr
module B = Dolmen.Std.Builtin
open Helpers
open Literals

(* Trigger selection intially intended to follow Pit-Claudel & Leino, "Trigger
   Selection Strategies to Stabilize Program Verifiers", Section 2 [1], then
   adapted through a more "heuristic" approach. *)

(* [Some x1; ...; Some xn] -> Some [x1;...;xn]; else None *)
let all_some l =
  if List.for_all Option.is_some l then Some (List.map Option.get l) else None

(* the type variable of the axiom being processed, reset for every new axiom
   (the initial value is a placeholder) *)
let current_fp_tyvar : DE.Ty.Var.t ref = ref (DE.Ty.Var.mk "ae.fp.t")

(* true for smt-lib and alt-ergo builtin symbols, never real trigger heads
   (called "trigger killers" in [1]). *)
let is_interpreted_symbol (c : DE.Term.Const.t) =
  (match c.builtin with B.Base -> false | _ -> true)
  || List.exists (String.equal (cst_path_name c)) ae_builtin_syms

let is_interpreted_term (t : DE.Term.t) =
  match t.term_descr with
  | DE.App ({ term_descr = Cst c; _ }, _, _) -> is_interpreted_symbol c
  | _ -> false

(* true if a and b are among the known mutually exclusive symbols (currently
   only is_positive and is_negative are in the list) *)
let are_mutually_exclusif a b =
  List.exists
    (fun (x, y) ->
      (String.equal a x && String.equal b y)
      || (String.equal a y && String.equal b x))
    ["ae.fp.is_positive", "ae.fp.is_negative"]

(* used to check that a term has current_fp_tyvar as a type, i.e. produces fp
   values *)
let is_fp_producer (t : DE.Term.t) =
  match t.term_ty.ty_descr with
  | DE.TyVar v -> DE.Ty.Var.equal v !current_fp_tyvar
  | _ -> false

(* t = f(a1,...,an) -> [a1;...;an] | _ -> [] *)
let get_op_args (f : 'a B.Prop.t) (t : DE.Term.t) =
  match t.term_descr with
  | DE.App ({ term_descr = Cst { builtin = B.Prop f'; _ }; _ }, _, args)
    when f' = f ->
    (* TODO: should be safe but maybe avoid polymorphic equality *)
    args
  | _ -> []

(* not (p1 /\ ... /\ pn) -> [p1;...;pn] | _ -> [] *)
let get_neg_and_args (e : DE.Term.t) =
  match get_op_args B.Prop.Neg e with
  | [inner] -> get_op_args B.Prop.And inner
  | _ -> []

(* p1 \/ ... \/ pn        -> ([p1;...;pn], true)
 * not (p1 /\ ... /\ pn)  -> ([p1;...;pn], true)
 * otherwise              -> ([t], false) *)
let flattern_disj (t : DE.Term.t) =
  match get_op_args B.Prop.Or t with
  | [] -> ( match get_neg_and_args t with [] -> [t], false | l -> l, true)
  | l -> l, true

(* When the axiom is of the form `p1 \/ ... \/ pn [=> q]` select an alternative
   trigger with each pi, i in 1 .. n *)
let hyp_disjuncts (t : DE.Term.t) =
  let h = match get_op_args B.Prop.Imply t with [h; _] -> h | _ -> t in
  match flattern_disj h with l, true -> Some l | _, false -> None

let get_app_name (t : DE.Term.t) =
  match t.term_descr with
  | DE.App ({ term_descr = Cst c; _ }, _, _) -> Some (cst_path_name c)
  | _ -> None

let is_comparison_op t =
  match get_app_name t with
  | Some h -> List.mem h fp_comparison_relations
  | None -> false

let rec flatten_conj (t : DE.Term.t) =
  match get_op_args B.Prop.And t with
  | [] -> [t]
  | l -> List.concat_map flatten_conj l

let split_app (t : DE.Term.t) =
  match t.term_descr with
  | DE.App ({ term_descr = Cst c; _ }, _, args) -> Some (cst_path_name c, args)
  | _ -> None

let rec term_size (t : DE.Term.t) =
  match t.term_descr with
  | DE.Var _ | DE.Cst _ -> 1
  | DE.App (f, _, args) ->
    List.fold_left (fun n a -> n + term_size a) (1 + term_size f) args
  | DE.Binder (_, body) -> 1 + term_size body
  | DE.Match (t, cases) ->
    List.fold_left
      (fun n (_, branch) -> n + term_size branch)
      (1 + term_size t)
      cases

let apps_clash a b =
  match split_app a, split_app b with
  | Some (ha, argsa), Some (hb, argsb) ->
    are_mutually_exclusif ha hb && List.for_all2 DE.Term.equal argsa argsb
  | _ -> false

(* true if a pair in [l] are contradictory (i.e. two apps that can't be true at
   the same time appear) because such an instantiation would be infeasible *)
let rec are_contradictory = function
  | [] -> false
  | a :: rest -> List.exists (apps_clash a) rest || are_contradictory rest

let group_by_head items =
  let grouped = Hashtbl.create 8 in
  List.iter
    (fun f ->
      match get_app_name f with
      | Some name ->
        let old =
          match Hashtbl.find_opt grouped name with Some l -> l | None -> []
        in
        Hashtbl.replace grouped name (f :: old)
      | None -> ())
    items;
  grouped

(* groups of [cands] sharing a head symbol that occurs 2+ times, one group per
   symbol. *)
let all_repeated_heads cands =
  let grouped = group_by_head cands in
  let seen = Hashtbl.create 8 in
  List.filter_map
    (fun t ->
      match get_app_name t with
      | Some name when not (Hashtbl.mem seen name) -> (
        Hashtbl.add seen name ();
        match Hashtbl.find_opt grouped name with
        | Some atoms when List.length atoms >= 2 -> Some (List.rev atoms)
        | _ -> None)
      | _ -> None)
    cands

(* every uninterpreted application in [t], in order of appearance,
   trigger-killers are dropped. *)
let collect_cands (t : DE.Term.t) : DE.Term.t list =
  let rec aux acc (t : DE.Term.t) =
    match t.term_descr with
    | DE.App ({ term_descr = Cst c; _ }, _, args) when is_interpreted_symbol c
      ->
      List.fold_left aux acc args
    | DE.App ({ term_descr = Cst _; _ }, _, args) ->
      List.fold_left aux (t :: acc) args
    | DE.App (f, _, args) -> List.fold_left aux (aux acc f) args
    | _ -> acc
  in
  List.rev (aux [] t)

(* greedily cover [qvars] with [cands]; when a pick covers a set S, descend into
   a sub-term covering the same S if one exists (parsimony [1]). None if some
   variable stays uncovered. *)
let greedy_cover qvars cands : DE.Term.t list option =
  let mem_var v l = List.exists (DE.Term.Var.equal v) l in
  let contrib uncovered t =
    List.filter (fun v -> term_uses_vars [v] t) uncovered
  in
  let subset l1 l2 = List.for_all (fun v -> mem_var v l2) l1 in
  let rec refine uncovered add (pick : DE.Term.t) =
    let subs =
      match pick.term_descr with
      | DE.App (_, _, args) -> List.concat_map collect_cands args
      | _ -> []
    in
    match
      List.rev (List.filter (fun d -> subset add (contrib uncovered d)) subs)
    with
    | d :: _ -> refine uncovered add d
    | [] -> pick
  in
  let rec aux uncovered acc cands =
    if uncovered = []
    then Some (List.rev acc)
    else
      match cands with
      | [] -> None
      | c :: rest ->
        let add = contrib uncovered c in
        if add = []
        then aux uncovered acc rest
        else
          let pick = refine uncovered add c in
          let uncovered =
            List.filter (fun v -> not (mem_var v add)) uncovered
          in
          aux uncovered (pick :: acc) rest
  in
  aux qvars [] cands

(* `r(x,y) /\ r(y,x) /\ ... => q`: same relation repeated 2+ times in the
   hypothesis, each occurrence covering by itself -> multi-trigger on all of
   them. *)
let same_relation_multi qvars (body : DE.Term.t) : DE.Term.t list list option =
  match get_op_args B.Prop.Imply body with
  | [hyp; _] -> (
    let full =
      List.filter
        (fun t -> term_uses_all_vars qvars t && not (is_interpreted_term t))
        (flatten_conj hyp)
    in
    (* They all work here so just take the first one *)
    match all_repeated_heads full with
    | g :: _ -> Some [g]
    | [] -> None)
  | _ -> None

(* `hyp = c1 /\ ... /\ cn`, where at least one ci is a disjunction of the form
   `ci = ci_1 \/ ci_2 \/ ...`, pick one branch from each disjunctive ci and pair
   it up across every such ci, one combination per pairing (e.g. `[c1_1; ...;
   cn_1]`, `[c1_1; ...; cn_2]`, `[c1_2; ...; cn_1]`, `[c1_2; ...; cn_2]`). Drop
   the combinations that are contradictory, then build one trigger per surviving
   combination. Skipped if some candidate already covers alone,
   [fp_producer_or_fallback] handles the simpler cases. *)
let hyp_conj_disj_product qvars (body : DE.Term.t) (cands : DE.Term.t list) :
    DE.Term.t list list option =
  if List.exists (term_uses_all_vars qvars) cands
  then None
  else
    match get_op_args B.Prop.Imply body with
    | [hyp; _] -> (
      let conjuncts = flatten_conj hyp in
      let alt_lists = List.map flattern_disj conjuncts in
      let n_disj = List.length (List.filter snd alt_lists) in
      if n_disj < 1
      then None
      else
        let combos =
          List.fold_left
            (fun combos (alts, _) ->
              List.concat_map (fun c -> List.map (fun a -> a :: c) alts) combos)
            [[]] alt_lists
        in
        let flat_combos = List.map (List.concat_map flatten_conj) combos in
        match
          List.filter (fun atoms -> not (are_contradictory atoms)) flat_combos
        with
        | [] -> None
        | survivors -> (
          match
            List.filter_map
              (fun atoms ->
                greedy_cover qvars (List.concat_map collect_cands atoms))
              survivors
          with
          | [] -> None
          | pats -> Some pats))
    | _ -> None

(* If every full-covering candidate is le/lt/eq, but some other candidate is
   fp-producing, redirect to that one instead, since le/lt/eq are reused
   everywhere and match too much, use le/lt/eq if there is no choice. *)
let fp_head_multi qvars (cands : DE.Term.t list) : DE.Term.t list option =
  let full = List.filter (term_uses_all_vars qvars) cands in
  if full = [] || not (List.for_all is_comparison_op full)
  then None
  else if not (List.exists is_fp_producer cands)
  then None
  else
    (* prioritize fp-producing candidates first *)
    let pool = List.filter (fun c -> not (is_comparison_op c)) cands in
    let fp, rest = List.partition is_fp_producer pool in
    greedy_cover qvars (fp @ rest)

(* Special case: `to_int(of_int(i)) = i`: select the outer to_int, not the
   of_int argument else it will match on every of_int term *)
let to_int_of_int_inverse qvars (cands : DE.Term.t list) :
    DE.Term.t list list option =
  let is_to_int_of_int (t : DE.Term.t) =
    match t.term_descr with
    | DE.App ({ term_descr = Cst c; _ }, _, args)
      when String.equal (cst_path_name c) "ae.fp.to_int" -> (
      match List.rev args with
      | last :: _ -> (
        match get_app_name last with
        | Some h -> String.equal h "ae.fp.of_int"
        | None -> false)
      | [] -> false)
    | _ -> false
  in
  match List.find_opt is_to_int_of_int cands with
  | Some t when term_uses_all_vars qvars t -> Some [[t]]
  | _ -> None

let fp_producer_or_fallback qvars cands : DE.Term.t list list option =
  let full = List.filter (term_uses_all_vars qvars) cands in
  match List.filter is_fp_producer full with
  | [] -> (
    match fp_head_multi qvars cands with
    | Some pat -> Some [pat]
    | None -> (
      match full with
      | f :: _ -> Some [[f]]
      | [] -> (
        (* nothing covers alone: greedy multi-term, or same-head if smaller *)
        let plain = greedy_cover qvars cands in
        let alt =
          (* no single candidate covers alone, but 2+ occurrences of one symbol
             jointly do, try each repeated head, keep the first that covers *)
          List.find_map (greedy_cover qvars) (all_repeated_heads cands)
        in
        match plain, alt with
        | Some p, Some a when List.length a < List.length p -> Some [a]
        | Some p, _ -> Some [p]
        | None, _ -> None)))
  | [p] -> Some [[p]]
  | hd :: _ as prod ->
    (* among several fully-covering fp-producing candidates, take the smallest
       (least likely to have extra/unnecessary terms) *)
    let found, _ =
      List.fold_left
        (fun (t_acc, s_acc) t ->
          let ts = term_size t in
          if ts < s_acc then t, ts else t_acc, s_acc)
        (hd, term_size hd)
        prod
    in
    Some [[found]]

(* try each rule in turn, stop at the first that succeeds *)
let select_triggers qvars (body : DE.Term.t) : DE.Term.t list list =
  match hyp_disjuncts body with
  | Some l ->
    let pats = List.map (fun d -> greedy_cover qvars (collect_cands d)) l in
    Option.value ~default:[] (all_some pats)
  | None ->
    let cands = collect_cands body in
    let selectors =
      [ (fun () -> same_relation_multi qvars body);
        (fun () -> hyp_conj_disj_product qvars body cands);
        (fun () -> to_int_of_int_inverse qvars cands);
        (fun () -> fp_producer_or_fallback qvars cands) ]
    in
    Option.value ~default:[] (List.find_map (fun rule -> rule ()) selectors)

(* Select triggers from the body, unless one is already set. *)
let process_axiom ~fp_tyvar qvars (inner : DE.Term.t) : unit =
  current_fp_tyvar := fp_tyvar;
  match DE.Term.get_tag_list inner DE.Tags.triggers with
  | _ :: _ -> ()
  | [] -> (
    match select_triggers qvars inner with
    | [] -> ()
    | pats ->
      (* wrap any pattern with multiple terms as a multi-trigger *)
      DE.Term.set_tag inner DE.Tags.triggers
        (List.map (function [t] -> t | ts -> DE.Term.multi_trigger ts) pats))
