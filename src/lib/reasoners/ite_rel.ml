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

open Options

module E = Expr

module Ex = Explanation

module EX2 = struct
  type t = E.t * E.t
  let compare (s1, s2) (t1, t2) =
    let c = E.compare s1 t1 in
    if c <> 0 then c else E.compare s2 t2
end

module ME2 = Map.Make(EX2)
module SE2 = Set.Make(EX2)
module ME = Expr.Map

module TB =
  Map.Make
    (struct
      type t = E.t * bool
      let compare (a1, b1) (a2, b2) =
        let c = E.compare a1 a2 in
        if c <> 0 then c else Bool.compare b1 b2
    end)

let src = Logs.Src.create ~doc:"Ite_rel" __MODULE__
module Log = (val Logs.src_log src : Logs.LOG)

let timer = Timers.M_Ite

(* The present theory simplifies the ite terms t of the form
    ite(pred, t1, t2)
   where pred is an assumed predicate by introducing the equation
   t = t1 or t = t2 according to the truth value of pred. *)

type t = {
  pending_deds      : Ex.t ME2.t;
  (* Map of pending deductions to their explanation. A deduction is an equation
     of the form t = b where t is an ite term and b is one of its branches.
     A deduction is added to pending_deds if the condition of the ite term
     is entailed by the current state of the solver. If so, the appropriate
     branch is selected according to the truth value of the condition. *)

  guarded_pos_deds  : SE2.t ME.t;
  (* Map of the condition of ite terms to its if branch.
     This map contains only condition that was not entailed yet by the
     current state of the solver during the registration of the ite term. *)

  guarded_neg_deds  : SE2.t ME.t;
  (* Map of the condition of ite terms to its else branch.
     This map contains only condition whose the negation was not entailed yet
     by the current state of the solver during the registration of the ite
     term. *)

  assumed_pos_preds : Ex.t ME.t;
  (* Map of all the predicates entailed by the current state of the solver to
     their explanation. *)

  assumed_neg_preds : Ex.t ME.t;
  (* Map of all the predicates whose the negation is entailed by the current
     state of the solver to their explanation. *)
}

let empty uf = {
  pending_deds      = ME2.empty;
  guarded_pos_deds  = ME.empty;
  guarded_neg_deds  = ME.empty;
  assumed_pos_preds = ME.empty;
  assumed_neg_preds = ME.empty;
}, Uf.domains uf

let is_ite =
  let ite = Symbols.Op Symbols.Tite in
  fun t ->
    match E.term_view t with
    | { E.f ; xs = [p;t1;t2]; _ } when Symbols.equal f ite -> Some (p, t1, t2)
    | _ -> None

let add_to_guarded p s t mp =
  let st = try ME.find p mp with Not_found -> SE2.empty in
  ME.add p (SE2.add (s, t) st) mp

(* Check if the condition of the ite t is a predicate entailed by the current
   state of the solver. If so, select the appropriate branch b of the ite and
   produce the deduction t = b. Otherwise save the if and else branches of t
   in order to retrieve them quickly in the assume function. *)
let add_aux env t =
  if Options.get_disable_ites () then env
  else
    match is_ite t with
    | None -> env
    | Some (p, t1, t2) ->
      if get_debug_ite () then
        Printer.print_dbg
          ~module_name:"Ite_rel" ~function_name:"add_aux"
          "(if %a then %a else %a)"
          E.print p E.print t1 E.print t2;
      try
        let ex = ME.find p env.assumed_pos_preds in
        {env with pending_deds = ME2.add (t, t1) ex env.pending_deds}
      with Not_found ->
      try
        let ex = ME.find p env.assumed_neg_preds in
        {env with pending_deds = ME2.add (t, t2) ex env.pending_deds}
      with Not_found ->
        let guarded_pos_deds = add_to_guarded p t t1 env.guarded_pos_deds in
        let guarded_neg_deds = add_to_guarded p t t2 env.guarded_neg_deds in
        {env with guarded_pos_deds; guarded_neg_deds}

let add env uf _ t =
  add_aux env t, Uf.domains uf, []

(* Extract all the assumed predicates with their explanation from the input of
   the function assume below. *)
let extract_preds env la =
  List.fold_left
    (fun acc (_ra, root, expl, _orig) ->
       match root with
       | None -> acc
       | Some a ->
         match E.lit_view a with
         | E.Pred (t, is_neg)
           when not (ME.mem t env.assumed_pos_preds) &&
                not (ME.mem t env.assumed_neg_preds) ->
           if get_debug_ite () then
             Printer.print_dbg
               ~module_name:"Ite_rel" ~function_name:"assume"
               "%a" E.print a;
           TB.add (t, is_neg) expl acc
         | _ -> acc
    )TB.empty la

(* Transform the pending deductions into facts in order to return them in the
   function assume below. *)
let extract_pending_deductions env =
  let l =
    ME2.fold
      (fun (s, t) ex acc ->
         let a = E.mk_eq ~iff:false s t
                 [@ocaml.ppwarning "TODO: build IFF instead ?"]
         in
         if get_debug_ite () then
           Printer.print_dbg
             ~module_name:"Ite_rel" ~function_name:"assume"
             "deduce that %a with expl %a"
             E.print a Ex.print ex;
         (Literal.LTerm a, ex, Th_util.Other) :: acc)
      env.pending_deds []
  in
  {env with pending_deds = ME2.empty}, l

(* Save in the environment env all the assumed predicates of la. Produce new
   deductions implied by these new assumed predicates.
   Eventually, return all the pending deductions. *)
let assume env uf la =
  if Options.get_disable_ites () then
    env, Uf.domains uf, { Sig_rel.assume = []; remove = [] }
  else
    let env =
      TB.fold
        (fun (t, is_neg) ex env ->
           if is_neg then
             let assumed_neg_preds = ME.add t ex env.assumed_neg_preds in
             let deds =
               try ME.find t env.guarded_neg_deds
               with Not_found -> SE2.empty
             in
             let pending_deds =
               SE2.fold (fun e acc -> ME2.add e ex acc) deds env.pending_deds
             in
             {env with assumed_neg_preds; pending_deds}
           else
             let assumed_pos_preds = ME.add t ex env.assumed_pos_preds in
             let deds =
               try ME.find t env.guarded_pos_deds
               with Not_found -> SE2.empty
             in
             let pending_deds =
               SE2.fold (fun e acc -> ME2.add e ex acc) deds env.pending_deds
             in
             {env with assumed_pos_preds; pending_deds}
        )(extract_preds env la) env
    in
    let env, deds = extract_pending_deductions env in
    env, Uf.domains uf, { Sig_rel.assume = deds; remove = [] }

let case_split _env _uf ~for_model:_ = []

let optimizing_objective _env _uf _o = None

let query _ _ _ = None

let new_terms _ = E.Set.empty
let instantiate ~do_syntactic_matching:_ _ env _ _ = env, []

let assume_th_elt t _ _ = t
