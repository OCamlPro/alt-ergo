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

module X = Shostak.Combine
module Ex = Explanation
module E = Expr
module A = Xliteral
module LR = Uf.LX
module SE = Expr.Set
module Sy = Symbols
module CC_X = Ccx.Main
module L = Shostak.Literal

open Alias.Dolmen

module type S = sig
  type t

  val empty : unit -> t

  (* the first int is the decision level (dlvl) and the second one is the
     propagation level (plvl). The facts (first argument) are sorted in
     decreasing order with respect to (dlvl, plvl) *)
  val assume :
    ?ordered:bool ->
    (L.t * Th_util.lit_origin * Explanation.t * int * int) list -> t ->
    t * Expr.Set.t * int

  val add_objective : t -> Objective.Function.t -> Objective.Value.t -> t
  val query : E.t -> t -> Th_util.answer
  val cl_extract : t -> Expr.Set.t list
  val extract_ground_terms : t -> Expr.Set.t
  val get_real_env : t -> Ccx.Main.t
  val get_case_split_env : t -> Ccx.Main.t
  val do_optimize :
    acts:Shostak.Literal.t Th_util.acts -> t -> unit
  val do_case_split :
    ?acts:Shostak.Literal.t Th_util.acts ->
    t -> Util.case_split_policy -> t * Expr.Set.t

  val add_term : t -> Expr.t -> add_in_cs:bool -> t
  val compute_concrete_model :
    acts:Shostak.Literal.t Th_util.acts -> t -> unit
  val extract_concrete_model :
    declared_ids:Id.typed list ->
    t ->
    Models.t Lazy.t * Objective.Model.t

  val assume_th_elt : t -> Expr.th_elt -> Explanation.t -> t
  val theories_instances :
    do_syntactic_matching:bool ->
    Matching_types.info Expr.Map.t * Expr.t list Expr.Map.t Symbols.Map.t ->
    t -> (Expr.t -> Expr.t -> bool) ->
    int -> int -> t * Sig_rel.instances

  val get_assumed : t -> E.Set.t
  val reinit_cpt : unit -> unit
  val get_objectives : t -> Objective.Model.t
end

module Main_Default : S = struct

  type choice_sign =
    | CPos of Ex.exp (* The explication of this choice *)
    | CNeg (* The choice has been already negated *)


  type choice =
    X.r Xliteral.view * Th_util.lit_origin * choice_sign * Ex.t
  (** the choice, the size, choice_sign,  the explication set,
        the explication for this choice. *)

  let pp_choice ppf (sem_lit, lit_orig, _, ex) =
    let sem_lit = LR.make sem_lit in
    match (lit_orig : Th_util.lit_origin) with
    | CS (k, _) ->
      Fmt.pf ppf "%a cs: %a (because %a)"
        Th_util.pp_theory k LR.print sem_lit Ex.print ex
    | NCS (k, _) ->
      Fmt.pf ppf "%a ncs: %a (because %a)"
        Th_util.pp_theory k LR.print sem_lit Ex.print ex
    | _ -> assert false

  (*BISECT-IGNORE-BEGIN*)
  module Debug = struct
    open Printer

    let subterms_of_assumed l =
      List.fold_left
        (List.fold_left
           (fun st (a, _, _) ->
              match L.view a with
              | LTerm a ->
                Expr.Set.union st (E.sub_terms SE.empty a)
              | LSem _ -> st)
        )SE.empty l

    let types_of_subterms st =
      SE.fold (fun t acc -> Ty.Set.add (E.type_info t) acc) st Ty.Set.empty

    let generalize_types ty1 ty2 = match ty1, ty2 with
      | Ty.Tvar _, _ -> ty1
      | _, Ty.Tvar _ -> ty2
      | _ -> Ty.fresh_tvar ()

    let logics_of_assumed st =
      (* NB: using an [Hstring.Map] here depends on the fact that name mangling
         is done pre-emptively in [Symbols.name] *)
      SE.fold
        (fun t mp ->
           match E.term_view t with
           | { E.f = Sy.Name { hs; kind = ((Sy.Ac | Sy.Other) as is_ac); _ };
               xs; ty; _ } ->
             let xs = List.map E.type_info xs in
             let xs, ty =
               try
                 let xs', ty', is_ac' = Hstring.Map.find hs mp in
                 assert (is_ac == is_ac');
                 let ty = generalize_types ty ty' in
                 let xs =
                   try List.map2 generalize_types xs xs' with _ -> assert false
                 in
                 xs, ty
               with Not_found -> xs, ty
             in
             Hstring.Map.add hs (xs, ty, is_ac) mp

           | _ -> mp
        ) st Hstring.Map.empty

    module Ty_map = Map.Make (DE.Ty.Const)

    let types_of_assumed sty =
      let open Ty in
      Ty.Set.fold
        (fun ty mp ->
           match ty with
           | Tint | Treal | Tbool | Tbitv _ | Tfarray _ -> mp
           | Tvar _ -> assert false

           | Text (_, hs) | Trecord { name = hs; _ } when
               Ty_map.mem hs mp -> mp

           | Text (l, hs) ->
             let l = List.map (fun _ -> Ty.fresh_tvar()) l in
             Ty_map.add hs (Text(l, hs)) mp

           | Trecord { name; _ } ->
             (* cannot do better for records ? *)
             Ty_map.add name ty mp

           | Tadt (hs, _) ->
             (* cannot do better for ADT ? *)
             Ty_map.add hs ty mp
        )sty Ty_map.empty

    let print_types_decls ?(header=true) types =
      let open Ty in
      print_dbg ~flushed:false ~header "@[<v 2>(* types decls: *)@ ";
      Ty_map.iter
        (fun _ ty ->
           match ty with
           | Tint | Treal | Tbool | Tbitv _ | Tfarray _ -> ()
           | Tvar _ -> assert false
           | Text _ -> print_dbg ~flushed:false "type %a@ " Ty.print ty
           | Trecord { Ty.lbs; _ } ->
             print_dbg ~flushed:false ~header:false "type %a = " Ty.print ty;
             begin match lbs with
               | [] -> assert false
               | (lbl, ty)::l ->
                 let print fmt (lbl,ty) =
                   Format.fprintf fmt " ; %a :%a"
                     DE.Term.Const.print lbl Ty.print ty in
                 print_dbg ~flushed:false ~header:false
                   "{ %a : %a%a"
                   DE.Term.Const.print lbl Ty.print ty
                   (pp_list_no_space print) l;
                 print_dbg ~flushed:false ~header:false " }@ "
             end
           | Tadt _ ->
             print_dbg ~flushed:false ~header:false "%a@ " Ty.print_full ty
        )types;
      print_dbg ~header:false "@]"

    let print_arrow_type fmt xs =
      match xs with
      | [] -> ()
      | e :: l ->
        Format.fprintf fmt "%a" Ty.print e;
        List.iter (Format.fprintf fmt ", %a" Ty.print) l;
        Format.fprintf fmt " -> "

    let print_logics ?(header=true) logics =
      print_dbg ~header "@[<v 2>(* logics: *)@ ";
      Hstring.Map.iter
        (fun hs (xs, ty, is_ac) ->
           print_dbg ~flushed:false ~header:false
             "logic %s%s : %a%a@ "
             (if is_ac == Sy.Ac then "ac " else "")
             (Hstring.view hs)
             print_arrow_type xs
             Ty.print ty
        )logics;
      print_dbg ~header:false "@]"

    let print_declarations ?(header=true) l =
      let st = subterms_of_assumed l in
      let sty = types_of_subterms st in
      let types = types_of_assumed sty in
      let logics = logics_of_assumed st in
      print_types_decls ~header types;
      print_logics ~header logics

    let assumed, reinit_cpt =
      let cpt = ref 0 in
      let assumed l =
        if Options.get_debug_cc () then begin
          print_dbg ~module_name:"Theory" ~function_name:"assumed"
            "Assumed facts (in this order):";
          print_declarations ~header:false l;
          incr cpt;
          print_dbg ~flushed:false ~header:false "goal g_%d :@ " !cpt;
          List.iter
            (fun l ->
               print_dbg ~flushed:false ~header:false "(* call to assume *)@ ";
               match List.rev l with
               | [] -> assert false
               | (a,dlvl,plvl)::l ->
                 print_dbg ~flushed:false ~header:false
                   "( (* %d , %d *) %a "
                   dlvl plvl
                   L.pp a;
                 List.iter
                   (fun (a, dlvl, plvl) ->
                      print_dbg ~flushed:false ~header:false
                        " and@ (* %d , %d *) %a "
                        dlvl plvl
                        L.pp a
                   ) l;
                 print_dbg ~flushed:false ~header:false ") ->@ "
            ) (List.rev l);
          print_dbg ~header:false "false";
        end
      in
      let reinit_cpt () =
        cpt := 0
      in
      assumed, reinit_cpt

    let made_choices ppf choices =
      Fmt.pf ppf "@[<v 2>Stack of choices:@ %a@]" (Fmt.list pp_choice) choices

    let begin_case_split choices =
      if Options.get_debug_split () then
        print_dbg
          ~module_name:"Theory" ~function_name:"begin_case_split"
          "%a"
          made_choices choices

    let end_case_split choices =
      if Options.get_debug_split () then
        print_dbg
          ~module_name:"Theory" ~function_name:"end_case_split"
          "%a"
          made_choices choices

    (* unused --
       let split_size sz =
       if get_debug_split () then
        print_dbg
        ">size case-split: %s" (Numbers.Q.to_string sz)
    *)

    let print_lr_view fmt ch = LR.print fmt (LR.make ch)

    let split_backtrack neg_c ex_c =
      if Options.get_debug_split () then
        print_dbg
          ~module_name:"Theory" ~function_name:"split_backtrack"
          "I backtrack on %a : %a"
          print_lr_view neg_c Ex.print ex_c

    let split_assume c ex_c =
      if Options.get_debug_split () then
        print_dbg
          ~module_name:"Theory" ~function_name:"split assume"
          "I assume %a : %a"
          print_lr_view c Ex.print ex_c

    let split_backjump c dep =
      if Options.get_debug_split () then
        print_dbg
          ~module_name:"Theory" ~function_name:"split_backjump"
          "I backjump on %a : %a"
          print_lr_view c Ex.print dep

    let query a =
      if Options.get_debug_cc () then
        print_dbg
          ~module_name:"Theory" ~function_name:"query"
          "query : %a" E.print a

    let split_sat_contradicts_cs filt_choices =
      if Options.get_debug_split () then
        print_dbg
          ~module_name:"Theory" ~function_name:"split_sat_contradicts_cs"
          "The SAT contradicts CS! I'll replay choices@ %a"
          made_choices filt_choices

  end
  (*BISECT-IGNORE-END*)

  type t = {
    assumed_set : E.Set.t;
    assumed : (L.t * int * int) list list;
    cs_pending_facts :
      (L.t * Th_util.lit_origin * Ex.t * int * int) list list;
    terms : Expr.Set.t;
    gamma : CC_X.t;
    gamma_finite : CC_X.t;
    choices : choice list;
    objectives : Objective.Model.t;
  }

  let add_explanations_to_split (c, is_cs, size) =
    Steps.incr_cs_steps ();
    let exp = Ex.fresh_exp () in
    let ex_c_exp =
      if is_cs then Ex.add_fresh exp Ex.empty else Ex.empty
    in
    (* A new explanation in order to track the choice *)
    (c, size, CPos exp, ex_c_exp)

  let look_for_sat ~for_model env sem_facts new_choices =
    let rec generate_choices env sem_facts acc_choices =
      let new_splits, base_env =
        CC_X.case_split env.gamma_finite ~for_model
      in
      let env = { env with gamma_finite = base_env } in
      match new_splits with
      | [] ->
        (* We cannot make any progress as theories don't produce new
           case-splits and we don't find any inconsistencies. We may
           obtain a complete model of our problem. *)
        { env with choices = List.rev acc_choices }, sem_facts

      | _ ->
        let new_choices =
          List.map add_explanations_to_split new_splits
        in
        propagate_choices env sem_facts acc_choices new_choices

    (* Propagates the choice made by case-splitting to the environment
       [gamma_finite] of the CC(X) algorithm. If there is no more choices
       to propagate, we call the [generate_choices] to either generate more
       choices or leave the function.

       @raise [Inconsistent] if we detect an inconsistent with the choice
              on the top of [new_choices] but this choice doesn't
              participate to the inconsistency. *)
    and propagate_choices env sem_facts acc_choices new_choices =
      Options.exec_thread_yield ();
      Options.tool_req 3 "TR-CCX-CS-Case-Split";
      match new_choices with
      | [] -> generate_choices env sem_facts acc_choices

      | ((c, lit_orig, CNeg, ex_c) as a) :: new_choices ->
        let facts = CC_X.empty_facts () in
        CC_X.add_fact facts (LSem c, ex_c, lit_orig);
        let base_env, sem_facts =
          CC_X.assume_literals env.gamma_finite sem_facts facts
        in
        let env = { env with gamma_finite = base_env } in
        propagate_choices env sem_facts (a :: acc_choices) new_choices

      | ((c, lit_orig, CPos exp, ex_c_exp) as a) :: new_choices ->
        try
          Debug.split_assume c ex_c_exp;
          let facts = CC_X.empty_facts () in
          CC_X.add_fact facts (LSem c, ex_c_exp, lit_orig);
          let base_env, sem_facts =
            CC_X.assume_literals env.gamma_finite sem_facts facts
          in
          let env = { env with gamma_finite = base_env } in
          Options.tool_req 3 "TR-CCX-CS-Normal-Run";
          propagate_choices env sem_facts (a :: acc_choices) new_choices

        with Ex.Inconsistent (dep, classes) ->
        (* As we generate fresh explanation for each choice in
           [add_explanations_to_split], we know that the inconsistency involves
           the current choice if and only if the explanation [dep] contains
           the explanation exp. *)
        match Ex.remove_fresh exp dep with
        | None ->
          (* The choice doesn't participate to the inconsistency. *)
          Debug.split_backjump c dep;
          Options.tool_req 3 "TR-CCX-CS-Case-Split-Conflict";
          raise (Ex.Inconsistent (dep, classes))
        | Some dep ->
          Options.tool_req 3 "TR-CCX-CS-Case-Split-Progress";
          (* The choice participates to the inconsistency. *)
          let neg_c = LR.view (LR.neg (LR.make c)) in
          let lit_orig =
            match lit_orig with
            | Th_util.CS (k, sz) -> Th_util.NCS (k, sz)
            | _ ->
              (* Unreacheable as the exception [Inconsistent] is only
                 raised by [propagate_choices] on facts of origin
                 [Th_util.CS]. *)
              assert false
          in
          Debug.split_backtrack neg_c dep;
          if Options.get_bottom_classes () then
            Printer.print_dbg
              "bottom (case-split):%a"
              Expr.print_tagged_classes classes;
          propagate_choices env sem_facts acc_choices
            [neg_c, lit_orig, CNeg, dep]

    in
    propagate_choices env sem_facts (List.rev env.choices) new_choices

  (* remove old choices involving fresh variables that are no longer in UF *)
  let filter_valid_choice uf (ra, _, _, _) =
    let l = match ra with
      | A.Eq (r1, r2) -> [r1; r2]
      | A.Distinct (_, l) -> l
      | A.Builtin (_,_, l) -> l
      | A.Pred (p, _) -> [p]
    in
    List.for_all
      (fun r ->
         List.for_all
           (fun x ->
              match X.term_extract x with
              | Some t, _ -> Uf.mem uf t
              | _ -> true
           )(X.leaves r)
      )l

  (* 1. Remove case-split decisions contain fresh variables (introduced by
     theories solvers) that are not in the theories' environment anymore
     (because of backtrack)
     2. Remove implications that are due to decisions removed in 1. *)
  let filter_choices uf (choices : choice list) =
    let candidates_to_keep, to_ignore =
      List.partition (filter_valid_choice uf) choices in
    let ignored_decisions =
      List.fold_left
        (fun ex (_, _, ch, _) ->
           match ch with
           | CPos (Ex.Fresh _ as e) -> Ex.add_fresh e ex
           | CPos _ -> assert false
           | CNeg -> ex
        ) Ex.empty to_ignore
    in
    List.filter
      (fun (_ ,_ ,_ ,ex) ->
         try
           Ex.iter_atoms
             (function
               | Ex.Fresh _ as fr when Ex.mem fr ignored_decisions -> raise Exit
               | _ -> ()
             )ex;
           true
         with Exit -> (* ignore implicated related to ignored decisions *)
           false
      ) candidates_to_keep

  let reset_case_split_env t =
    { t with
      cs_pending_facts = []; (* be sure it's always correct when this
                                function is called *)
      gamma_finite = t.gamma; (* we'll take gamma directly *)
      choices = []; (* we'll not be able to attempt to replay
                       choices. We're not in try-it *)
    }

  (* This function attempts to produce a first-order model by case-splitting.
     To do so, the function tries two successive strategies:
     - First, we replay in [gamma_finite] all the new facts learnt by the
         SAT solver since the last case-splitting phase in the environment.
     - If the first strategy fails, we synchronize [gamma] and [gamma_finite]
         and we try to propagate a subset of the choices. *)
  let try_it t facts ~for_model =
    Options.exec_thread_yield ();
    Debug.begin_case_split t.choices;
    let r =
      try
        if t.choices == [] then
          (* We have not make choice yet. Initialize the environment
             [gamma_finite] with [gamma]. *)
          let t = reset_case_split_env t in
          look_for_sat ~for_model t [] []
        else
          begin
            try
              (* We attempt to replay all the facts learnt by the SAT solver
                 since the last call to [do_case_split]. *)
              let base_env, ch = CC_X.assume_literals t.gamma_finite [] facts in
              let t = { t with gamma_finite = base_env } in
              look_for_sat ~for_model t ch []
            with Ex.Inconsistent _ ->
              (* The inconsistency here doesn't mean there is no first-order
                 model of the problem in the current branch of the SAT solver.
                 For sake of soundness, we have to try to produce a model from
                 the current state of the SAT solver (using the environment
                 [gamma]). *)
              Options.tool_req 3 "TR-CCX-CS-Case-Split-Erase-Choices";
              (* We replay the conflict in look_for_sat, so we can
                 safely ignore the explanation which is not useful. *)
              let uf =  CC_X.get_union_find t.gamma in
              let filt_choices = filter_choices uf t.choices in
              Debug.split_sat_contradicts_cs filt_choices;
              let t = reset_case_split_env t in
              look_for_sat ~for_model
                { t with choices = [] } [] filt_choices
          end
      with Ex.Inconsistent (dep, classes) ->
        Debug.end_case_split t.choices;
        Options.tool_req 3 "TR-CCX-CS-Conflict";
        raise (Ex.Inconsistent (dep, classes))
    in
    Debug.end_case_split (fst r).choices; r


  let extract_from_semvalues acc l =
    List.fold_left
      (fun acc r ->
         match X.term_extract r with
         | Some t, _ -> SE.add t acc | _ -> acc) acc l

  let extract_terms_from_xliteral acc = function
    | A.Eq (r1, r2) -> extract_from_semvalues acc [r1; r2]
    | Distinct (_, l) -> extract_from_semvalues acc l
    | Pred (p, _) -> extract_from_semvalues acc [p]
    | _ -> acc

  let extract_terms_from_choices acc choices =
    List.fold_left
      (fun acc (a, _, _, _) ->
         extract_terms_from_xliteral acc a
      ) acc choices

  let extract_terms_from_assumed =
    List.fold_left
      (fun acc ((a : _ Sig_rel.literal), _, _) ->
         match a with
         | LTerm r -> begin
             match E.lit_view r with
             | E.Eq (t1, t2) ->
               SE.add t1 (SE.add t2 acc)
             | E.Eql l | E.Distinct l | E.Builtin (_, _, l) ->
               List.fold_right SE.add l acc
             | E.Pred (t1, _) ->
               SE.add t1 acc

           end
         | _ -> acc)

  let rec is_ordered_list l = match l with
    | [] | [[_]] -> true
    | []::r -> is_ordered_list r
    | [e]::r1::r2 -> is_ordered_list ((e::r1)::r2)
    | (e1::e2::l)::r ->
      let _, d1, p1 = e1 in
      let _, d2, p2 = e2 in
      (d1 > d2 || d1 = d2 && p1 > p2) && is_ordered_list ((e2::l)::r)

  let do_case_split_aux t ~for_model =
    let in_facts_l = t.cs_pending_facts in
    let t = {t with cs_pending_facts = []} in
    let facts = CC_X.empty_facts () in
    List.iter
      (List.iter
         (fun (a, o, ex,_dlvl,_plvl) ->
            let a =
              match L.view a with
              | LTerm _ as a -> a
              | LSem a -> LSem (LR.view a)
            in
            CC_X.add_fact facts (a, ex, o))
      ) in_facts_l;

    let t, ch = try_it t facts ~for_model in
    let choices = extract_terms_from_choices SE.empty t.choices in
    let choices_terms = extract_terms_from_assumed choices ch in

    {t with terms = Expr.Set.union t.terms choices_terms}, choices_terms

  let optimize_obj ~for_model add_objective obj t =
    let opt_split =
      Option.get (CC_X.optimizing_objective t.gamma obj)
    in
    match opt_split.value with
    | Unknown ->
      (* Cannot happen as [Rel.optimizing_objective] never returns an
         unknown value. *)
      assert false

    | Pinfinity | Minfinity | Limit _ when not for_model ->
      (* We stop optimizing the objective function [obj] in this case, but
         we continue to produce a model if the flag [for_model] is up. *)
      ()

    | Pinfinity | Minfinity | Limit _ | Value _ ->
      let (lview, is_cs, _) = opt_split.case_split in
      assert is_cs;

      if Options.get_debug_optimize () then
        Printer.print_dbg "Objective for %a is %a [split: %a]"
          Objective.Function.pp obj
          Objective.Value.pp opt_split.value
          Shostak.L.print (Shostak.L.make lview);

      add_objective
        obj opt_split.value
        (Shostak.(Literal.make @@ LSem (L.make lview)))

  let sat_splits t =
    if Options.get_enable_sat_cs () then
      let splits, gamma = CC_X.case_split t.gamma ~for_model:false in
      let splits =
        List.filter (fun (_, is_cs, origin) ->
            is_cs &&
            match origin with
            | Th_util.CS (Th_arrays, _) -> true
            | _ -> false
          ) splits
      in
      splits, { t with gamma }
    else
      [], t

  let do_optimize ~acts t =
    let objectives = t.objectives in
    match Objective.Model.next_unknown objectives with
    | Some obj ->
      let add_objective = acts.Th_util.acts_add_objective in
      optimize_obj ~for_model:false add_objective obj t
    | None -> ()

  let do_sat_splits acts t =
    let splits, t = sat_splits t in
    match splits with
    | [] -> do_case_split_aux t ~for_model:false
    | (lview, _, _) :: _ ->
      let lit = Shostak.(Literal.make @@ LSem (L.make lview)) in
      acts.Th_util.acts_add_split lit;
      t, SE.empty

  let do_case_split ?acts t origin =
    if Options.get_case_split_policy () == origin then
      match acts with
      | Some acts -> do_sat_splits acts t
      | None -> do_case_split_aux t ~for_model:false
    else
      t, SE.empty

  (* facts are sorted in decreasing order with respect to (dlvl, plvl) *)
  let assume ordered in_facts t =
    let facts = CC_X.empty_facts () in
    let assumed, assumed_set, cpt, gamma =
      List.fold_left
        (fun
          ((assumed, assumed_set, cpt, gamma) as accu)
          ((a, o, ex, dlvl, plvl))
          ->
            match L.view a with
            | Literal.LTerm a when E.Set.mem a assumed_set -> accu
            | aview ->
              let gamma, aview =
                match aview with
                | LTerm t -> gamma, Literal.LTerm t
                | LSem a ->
                  (* When assuming a semantic literal (typically a case split),
                     we may end up in cases where they contain terms that have
                     not been added.

                     One reason this can happen is when (the negation of)
                     semantic literals are pushed onto the trail at lower
                     levels than they were initially created (notably with
                     with minimal backjumps). *)
                  let aview = LR.view a in
                  let trms = extract_terms_from_xliteral SE.empty aview in
                  let gamma = SE.fold (fun t gamma ->
                      fst @@ CC_X.add_term gamma facts t Ex.empty
                    ) trms gamma in
                  gamma, LSem aview
              in
              CC_X.add_fact facts (aview, ex, o);
              let assumed_set =
                match aview with
                | LTerm a -> E.Set.add a assumed_set
                | _ -> assumed_set
              in
              (a, dlvl, plvl) :: assumed,
              assumed_set,
              cpt+1,
              gamma
        )([], t.assumed_set, 0, t.gamma) in_facts
    in
    if assumed == [] then t, E.Set.empty, 0
    else
      let t = {t with assumed_set; assumed = assumed :: t.assumed; gamma;
                      cs_pending_facts = in_facts :: t.cs_pending_facts} in
      if Options.get_profiling() then Profiling.assume cpt;
      Debug.assumed t.assumed;
      assert (not ordered || is_ordered_list t.assumed);
      let gamma, _ = CC_X.assume_literals t.gamma [] facts in
      let new_terms = CC_X.new_terms gamma in
      let t =  {t with
                gamma = gamma; terms = Expr.Set.union t.terms new_terms;
               }
      in
      t, new_terms, cpt

  let get_debug_theories_instances th_instances ilvl dlvl =
    let module MF = Expr.Map in
    Printer.print_dbg ~flushed:false
      ~module_name:"Theory" ~function_name:"theories_instances"
      "@[<v 2>dec. level = %d, instant.\
       level = %d, %d new Th instances@ "
      dlvl ilvl (List.length th_instances);
    let mp =
      List.fold_left
        (fun acc ((hyps:Expr.t list),gf, _) ->
           match gf.Expr.lem with
           | None -> assert false
           | Some lem ->
             let inst =
               try MF.find lem acc with Not_found -> MF.empty
             in
             MF.add lem (MF.add gf.Expr.ff hyps inst) acc
        )MF.empty th_instances
    in
    let l =
      MF.fold
        (fun f inst acc -> (f, MF.cardinal inst, inst) :: acc) mp []
    in
    let l = List.fast_sort (fun (_,m,_) (_,n,_) -> n - m) l in
    List.iter (fun (f, m, inst) ->
        Printer.print_dbg ~flushed:false ~header:false
          "%3d  -->  %a@ " m Expr.print f;
        if true then begin
          MF.iter
            (fun f hyps ->
               Printer.print_dbg ~flushed:false ~header:false
                 "@[<v 2>[inst]@ ";
               List.iter
                 (fun h ->
                    Printer.print_dbg ~flushed:false ~header:false
                      "hypothesis: %a@ " Expr.print h;
                 )hyps;
               Printer.print_dbg ~flushed:false ~header:false
                 "@]conclusion: %a@ " Expr.print f;
            ) inst
        end
      ) l;
    Printer.print_dbg ~header:false "@]"

  let theories_instances ~do_syntactic_matching t_match t selector dlvl ilvl =
    let gamma, instances =
      CC_X.theories_instances ~do_syntactic_matching t_match t.gamma selector in
    if Options.get_debug_fpa() > 0 then
      get_debug_theories_instances instances dlvl ilvl;
    {t with gamma = gamma}, instances

  let query =
    let add_and_process_conseqs a t =
      (* !!! query does not modify gamma_finite anymore *)
      Options.exec_thread_yield ();
      let gamma, facts = CC_X.add t.gamma (CC_X.empty_facts()) a Ex.empty in
      let gamma, _ = CC_X.assume_literals gamma [] facts in
      { t with gamma = gamma }
    in
    fun a t ->
      if Options.get_no_tcp () then None
      else begin
        if Options.get_profiling() then Profiling.query();
        Options.exec_thread_yield ();
        Debug.query a;
        try
          match E.lit_view a with
          | E.Eq (t1, t2)  ->
            let t = add_and_process_conseqs a t in
            CC_X.are_equal t.gamma t1 t2 ~init_terms:false

          | E.Distinct [t1; t2] ->
            let na = E.neg a in
            let t = add_and_process_conseqs na t in (* na ? *)
            CC_X.are_distinct t.gamma t1 t2

          | E.Distinct _ | E.Eql _ ->
            (* we only assume toplevel distinct with more that one arg.
               not interesting to do a query in this case ?? or query ? *)
            None

          | E.Pred (t1,b) ->
            let t = add_and_process_conseqs a t in
            if b
            then CC_X.are_distinct t.gamma t1 Expr.vrai
            else CC_X.are_equal t.gamma t1 Expr.vrai ~init_terms:false

          | _ ->
            let na = E.neg a in
            let t = add_and_process_conseqs na t in
            CC_X.query t.gamma na
        with Ex.Inconsistent (d, classes) ->
          Some (d, classes)
      end

  let add_term_in_gm gm t =
    let facts = CC_X.empty_facts() in
    let gm, facts = CC_X.add_term gm facts t Ex.empty in
    fst (CC_X.assume_literals gm [] facts) (* may raise Inconsistent *)

  let add_term env t ~add_in_cs =
    let gm = add_term_in_gm env.gamma t in
    if not add_in_cs then {env with gamma = gm}
    else {env with gamma=gm; gamma_finite=add_term_in_gm env.gamma_finite t}

  let empty () =
    let env = CC_X.empty in
    let env, _ = CC_X.add_term env (CC_X.empty_facts()) E.vrai Ex.empty in
    let env, _ = CC_X.add_term env (CC_X.empty_facts()) E.faux Ex.empty in
    let t =
      { gamma = env;
        gamma_finite = env;
        choices = [];
        assumed_set = E.Set.empty;
        assumed = [];
        cs_pending_facts = [];
        terms = Expr.Set.empty;
        objectives = Objective.Model.empty;
      }
    in
    let a = E.mk_distinct ~iff:false [E.vrai; E.faux] in
    let t, _, _ =
      assume true [L.make @@ Literal.LTerm a, Th_util.Other, Ex.empty, 0, -1] t
    in
    t

  let cl_extract env = CC_X.cl_extract env.gamma

  let assume ?(ordered=true) facts t =
    Timers.with_timer Timers.M_CC Timers.F_assume @@ fun () ->
    assume ordered facts t

  let query a t =
    Timers.with_timer Timers.M_CC Timers.F_query @@ fun () ->
    query a t

  let extract_ground_terms env = env.terms

  let get_real_env t = t.gamma
  let get_case_split_env t = t.gamma_finite

  let compute_concrete_model ~acts t =
    let add_objective = acts.Th_util.acts_add_objective in
    match Objective.Model.next_unknown t.objectives with
    | Some obj ->
      optimize_obj ~for_model:true add_objective obj t
    | None ->
      ()

  let extract_concrete_model ~declared_ids env =
    let { gamma_finite; assumed_set; objectives; _ }, _ =
      do_case_split_aux env ~for_model:true
    in
    lazy (
      CC_X.extract_concrete_model
        ~prop_model:assumed_set
        ~declared_ids
        gamma_finite
    ), objectives

  let assume_th_elt t th_elt dep =
    { t with gamma = CC_X.assume_th_elt t.gamma th_elt dep }

  let get_assumed env = env.assumed_set

  let get_objectives env = env.objectives

  let add_objective env fn value =
    (* We have to add the term [fn] and its subterms as the MaxSMT
       syntax allows to optimize expressions that are not part of
       the current context. *)
    let expr = fn.Objective.Function.e in
    let env = add_term env ~add_in_cs:false expr in
    (* We also have to add the term for matching. *)
    let terms = Expr.Set.add expr env.terms in
    let objectives = Objective.Model.add fn value env.objectives in
    { env with objectives; terms }

  let reinit_cpt () =
    Debug.reinit_cpt ()
end

module Main_Empty : S = struct

  type t =
    { assumed_set : E.Set.t }

  let empty () = { assumed_set = E.Set.empty }

  let assume ?ordered:(_=true) in_facts t =
    let assumed_set =
      List.fold_left
        (fun assumed_set ((a, _, _, _, _)) ->
           match L.view a with
           | LTerm a -> E.Set.add a assumed_set
           | LSem _ -> assumed_set
        ) t.assumed_set in_facts
    in
    {assumed_set}, E.Set.empty, 0

  let query _ _ = None

  let cl_extract _ = []
  let extract_ground_terms _ = Expr.Set.empty

  let get_real_env _ = CC_X.empty
  let get_case_split_env _ = CC_X.empty
  let do_optimize ~acts:_ _ = ()
  let do_case_split ?acts:_ env _ = env, E.Set.empty
  let add_term env _ ~add_in_cs:_ = env
  let compute_concrete_model ~acts:_ _env = ()
  let extract_concrete_model ~declared_ids:_ _env =
    lazy Models.empty, Objective.Model.empty

  let assume_th_elt e _ _ = e
  let theories_instances ~do_syntactic_matching:_ _ e _ _ _ = e, []
  let get_assumed env = env.assumed_set
  let add_objective env _fn _value = env
  let reinit_cpt () = ()

  let get_objectives _env = Objective.Model.empty
end
