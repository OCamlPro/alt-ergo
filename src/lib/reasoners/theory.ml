(**************************************************************************)
(*                                                                        *)
(*     Alt-Ergo: The SMT Solver For Software Verification                 *)
(*     Copyright (C) 2013-2023 --- OCamlPro SAS                           *)
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
(*     Until 2013, some parts of this code were released under            *)
(*     the Apache Software License version 2.0.                           *)
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

module type S = sig
  type t

  val empty : unit -> t

  (* the first int is the decision level (dlvl) and the second one is the
     propagation level (plvl). The facts (first argument) are sorted in
     decreasing order with respect to (dlvl, plvl) *)
  val assume :
    ?ordered:bool ->
    (E.t * Explanation.t * int * int) list -> t ->
    t * Expr.Set.t * int

  val query : E.t -> t -> Th_util.answer
  val cl_extract : t -> Expr.Set.t list
  val extract_ground_terms : t -> Expr.Set.t
  val get_real_env : t -> Ccx.Main.t
  val get_case_split_env : t -> Ccx.Main.t
  val do_case_split : t -> Util.case_split_policy -> t * Expr.Set.t
  val add_term : t -> Expr.t -> add_in_cs:bool -> t
  val compute_concrete_model :
    t ->
    Models.t Lazy.t option

  val assume_th_elt : t -> Expr.th_elt -> Explanation.t -> t
  val theories_instances :
    do_syntactic_matching:bool ->
    Matching_types.info Expr.Map.t * Expr.t list Expr.Map.t Symbols.Map.t ->
    t -> (Expr.t -> Expr.t -> bool) ->
    int -> int -> t * Sig_rel.instances

  val get_assumed : t -> E.Set.t
  val reinit_cpt : unit -> unit
  val get_objectives : t -> Th_util.optimized_split Util.MI.t
end

module Main_Default : S = struct

  type choice_sign =
    | CPos of Ex.exp (* The explication of this choice *)
    | CNeg (* The choice has been already negated *)


  type choice =
    X.r Xliteral.view * Th_util.lit_origin * choice_sign * Ex.t * int option
  (** the choice, the size, choice_sign,  the explication set,
        the explication for this choice. *)

  let pp_choice ppf (sem_lit, lit_orig, _, ex, ord) =
    let pp_ord ppf ord =
      match ord with
      | Some o -> Fmt.pf ppf "Optim-cs(ord=%d)" o
      | None -> ()
    in
    let sem_lit = LR.make sem_lit in
    match (lit_orig : Th_util.lit_origin) with
    | CS (k, _) ->
      Fmt.pf ppf "%a %a cs: %a (because %a)"
        Th_util.pp_theory k pp_ord ord LR.print sem_lit Ex.print ex
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
           (fun st (a, _, _) -> Expr.Set.union st (E.sub_terms SE.empty a))
        )SE.empty l

    let types_of_subterms st =
      SE.fold (fun t acc -> Ty.Set.add (E.type_info t) acc) st Ty.Set.empty

    let generalize_types ty1 ty2 = match ty1, ty2 with
      | Ty.Tvar _, _ -> ty1
      | _, Ty.Tvar _ -> ty2
      | _ -> Ty.fresh_tvar ()

    let logics_of_assumed st =
      SE.fold
        (fun t mp ->
           match E.term_view t with
           | { E.f = Sy.Name (hs, ((Sy.Ac | Sy.Other) as is_ac), _);
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

    let types_of_assumed sty =
      let open Ty in
      Ty.Set.fold
        (fun ty mp ->
           match ty with
           | Tint | Treal | Tbool | Tunit | Tbitv _ | Tfarray _ -> mp
           | Tvar _ -> assert false

           | Text (_, hs) | Tsum (hs, _) | Trecord { name = hs; _ } when
               Hstring.Map.mem hs mp -> mp

           | Text (l, hs) ->
             let l = List.map (fun _ -> Ty.fresh_tvar()) l in
             Hstring.Map.add hs (Text(l, hs)) mp

           | Tsum (hs, _) ->
             Hstring.Map.add hs ty mp

           | Trecord { name; _ } ->
             (* cannot do better for records ? *)
             Hstring.Map.add name ty mp

           | Tadt (hs, _) ->
             (* cannot do better for ADT ? *)
             Hstring.Map.add hs ty mp
        )sty Hstring.Map.empty

    let print_types_decls ?(header=true) types =
      let open Ty in
      print_dbg ~flushed:false ~header "@[<v 2>(* types decls: *)@ ";
      Hstring.Map.iter
        (fun _ ty ->
           match ty with
           | Tint | Treal | Tbool | Tunit | Tbitv _ | Tfarray _ -> ()
           | Tvar _ -> assert false
           | Text _ -> print_dbg ~flushed:false "type %a@ " Ty.print ty
           | Tsum (_, l) ->
             print_dbg ~flushed:false ~header:false "type %a = " Ty.print ty;
             begin match l with
               | [] -> assert false
               | e::l ->
                 let print fmt e =
                   Format.fprintf fmt " | %s" (Hstring.view e)
                 in
                 print_dbg ~flushed:false ~header:false "%s@ %a@ "
                   (Hstring.view e)
                   (pp_list_no_space print) l;
             end

           | Trecord { Ty.lbs; _ } ->
             print_dbg ~flushed:false ~header:false "type %a = " Ty.print ty;
             begin match lbs with
               | [] -> assert false
               | (lbl, ty)::l ->
                 let print fmt (lbl,ty) =
                   Format.fprintf fmt " ; %s :%a"
                     (Hstring.view lbl) Ty.print ty in
                 print_dbg ~flushed:false ~header:false
                   "{ %s : %a%a"
                   (Hstring.view lbl) Ty.print ty
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
                   E.print a;
                 List.iter
                   (fun (a, dlvl, plvl) ->
                      print_dbg ~flushed:false ~header:false
                        " and@ (* %d , %d *) %a "
                        dlvl plvl
                        E.print a
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
    assumed : (E.t * int * int) list list;
    cs_pending_facts : (E.t * Ex.t * int * int) list list;
    terms : Expr.Set.t;
    gamma : CC_X.t;
    gamma_finite : CC_X.t;
    choices : choice list;
    objectives : Th_util.optimized_split Util.MI.t;
  }

  let add_explanations_to_split (c, is_cs, size) =
    Steps.incr_cs_steps ();
    let exp = Ex.fresh_exp () in
    let ex_c_exp =
      if is_cs then Ex.add_fresh exp Ex.empty else Ex.empty
    in
    (* A new explanation in order to track the choice *)
    (c, size, CPos exp, ex_c_exp, None)

  let register_optimized_split objectives u =
    try
      let x = Util.MI.find u.Th_util.order objectives in
      assert (E.equal x.Th_util.e u.Th_util.e);
      (* and its Value ... *)
      Util.MI.add u.Th_util.order u objectives
    with Not_found ->
      assert false

  exception Found of Th_util.optimized_split

  (* TODO: this function could be optimized if "objectives" structure
     is coded differently *)
  let next_optimization ~for_model env =
    try
      Util.MI.iter (fun _ x ->
          match x.Th_util.value with
          | Value (_, None) ->
            (* This split is already optimized. *)
            ()
          | Pinfinity | Minfinity | Value (_, (Plus | Minus)) ->
            (* We should block case-split at infinite values.
                  Otherwise, we may have soundness issues. We
                  may think an objective is unbounded, but some late
                  constraints may make it bounded.

                  An alternative is to only allow further splits when we
                  know that no extra assumptions will be propagated to
                  the env. Hence the test 'if for_model' *)
            if for_model then ()
            else
              raise (Found { x with Th_util.value = Unknown })

          | Unknown ->
            raise (Found { x with Th_util.value = Unknown })

        ) env.objectives;
      None
    with
    | Found x -> Some x

  (* TODO: this function could be optimized if "objectives" structure
     is coded differently *)
  let partial_objectives_reset objectives order =
    match order with
    | None -> objectives
    | Some opt_ord ->
      Util.MI.fold
        (fun ord v acc ->
           if ord < opt_ord then
             (*don't change older optims that are still valid splits*)
             acc
           else
             match v.Th_util.value with
             | Th_util.Unknown -> acc (* not optimized yet *)
             | Value _ ->
               Util.MI.add ord {v with value = Unknown} acc
             | Pinfinity | Minfinity ->
               assert false (* may happen? *)
        ) objectives objectives

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
        aux env sem_facts acc_choices new_choices

    and optimizing_split env sem_facts acc_choices opt_split =
      let opt_split =
        CC_X.optimizing_split env.gamma_finite opt_split
      in
      let objectives =
        register_optimized_split env.objectives opt_split
      in
      let env = { env with objectives } in
      match opt_split.value with
      | Unknown ->
        (* In the current implementation of optimization, the function
           [CC_X.optimizing_split] cannot fail to optimize the split
           [opt_split]. First of all, the legacy parser only accepts
           optimization clauses on expressions of type [Real] or [Int].

           For the [Real] or [Int] expressions, we have two cases:
           - If the objective function is a linear functions of variables, the
             decision procedure implemented in Ocplib-simplex cannot fail to
             optimize the split. For instance, if we try to maximize the
             expression:
               5 * x + 2 * y + 3 where x and y are real variables,
             the procedure will success to produce the upper bound of [x] and
             [y] modulo the other constraints on it.

           - If the objective function isn't linear, the nonlinear part of the
             expression have seen as uninterpreted term of the arithemic theory.
             Let's imagine we try to maximize the expression:
               5 * x * x + 2 * y + 3,
             The objective function given to Ocplib-simplex looks like:
               5 * U + 2 * y + 3 where U = x * x
             and the procedure will optimize the problem in terms of U and y. *)
        assert false

      | Pinfinity | Minfinity | Value (_, (Plus | Minus)) ->
        (* We stop optimizing the split [opt_split] in this case, but
           we continue to produce a model if the flag [for_model] is up. *)
        if for_model then
          propagate_choices env sem_facts acc_choices []
        else
          { env with choices = List.rev acc_choices }, sem_facts

      | Value (_, None) ->
        begin
          match opt_split.case_split with
          | Some cs ->
            let new_choice = add_explanations_to_split cs in
            aux env sem_facts acc_choices [new_choice]
          | None -> assert false
        end

    (* Propagates the choice made by case-splitting to the environment
       [gamma_finite] of the CC(X) algorithm. If there is no more choices
       to propagate, we call the dispatcher [aux] to leave the function.

       @raise [Inconsistent] if we detect an inconsistent with the choice
              on the top of [new_choices] but this choice doesn't
              participate to the inconsistency. *)
    and propagate_choices env sem_facts acc_choices new_choices =
      Options.exec_thread_yield ();
      match new_choices with
      | [] -> aux env sem_facts acc_choices new_choices

      | ((c, lit_orig, CNeg, ex_c, _order) as a) :: new_choices ->
        let facts = CC_X.empty_facts () in
        CC_X.add_fact facts (LSem c, ex_c, lit_orig);
        let base_env, sem_facts =
          CC_X.assume_literals env.gamma_finite sem_facts facts
        in
        let env = { env with gamma_finite = base_env } in
        propagate_choices env sem_facts (a :: acc_choices) new_choices

      | ((c, lit_orig, CPos exp, ex_c_exp, order) as a) :: new_choices ->
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
          let objectives = partial_objectives_reset env.objectives order in
          let env = { env with objectives } in
          propagate_choices env sem_facts acc_choices
            [neg_c, lit_orig, CNeg, dep, order]

    and aux env sem_facts acc_choices new_choices =
      Options.tool_req 3 "TR-CCX-CS-Case-Split";
      match new_choices, next_optimization ~for_model env with
      | [], None ->
        generate_choices env sem_facts acc_choices
      | [], Some opt_split ->
        optimizing_split env sem_facts acc_choices opt_split
      | _ ->
        propagate_choices env sem_facts acc_choices new_choices
    in
    aux env sem_facts (List.rev env.choices) new_choices

  (* remove old choices involving fresh variables that are no longer in UF *)
  let filter_valid_choice uf (ra, _, _, _, _) =
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
        (fun ex (_, _, ch, _, _) ->
           match ch with
           | CPos (Ex.Fresh _ as e) -> Ex.add_fresh e ex
           | CPos _ -> assert false
           | CNeg -> ex
        ) Ex.empty to_ignore
    in
    List.filter
      (fun (_ ,_ ,_ ,ex , _) ->
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


  let reset_objectives objectives =
    Util.MI.map (fun x -> Th_util.({ x with value = Unknown }) ) objectives

  let reset_case_split_env t =
    { t with
      objectives = reset_objectives t.objectives;
      cs_pending_facts = []; (* be sure it's always correct when this
                                function is called *)
      gamma_finite = t.gamma; (* we'll take gamma directly *)
      choices = []; (* we'll not be able to attempt to replay
                       choices. We're not in try-it *)
    }

  let has_no_infinity objectives =
    Util.MI.for_all
      (fun _ {Th_util.value; _} ->
         match value with
         | Pinfinity | Minfinity -> false
         | Value _ | Unknown -> true
      ) objectives

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
          (* We haven't make choice yet. Initialize the environment
             [gamma_finite] with [gamma]. *)
          let t = reset_case_split_env t in
          look_for_sat ~for_model t [] []
        else
          try
            (* We attempt to replay all the facts learnt by the SAT solver
               since the last call to [do_case_split]. *)
            let base_env, ch = CC_X.assume_literals t.gamma_finite [] facts in
            let t = { t with gamma_finite = base_env } in
            look_for_sat ~for_model t ch []
          with Ex.Inconsistent _ ->
            (* The inconsistency here doesn't mean there is no first-order model
               of the problem in the current branch of the SAT solver. For sake
               of soundness, we have to try to produce a model from the current
               state of the SAT solver (using the environment [gamma]). *)
            Options.tool_req 3 "TR-CCX-CS-Case-Split-Erase-Choices";
            (* We replay the conflict in look_for_sat, so we can
               safely ignore the explanation which is not useful. *)
            let uf =  CC_X.get_union_find t.gamma in
            let filt_choices = filter_choices uf t.choices in
            let filt_choices =
              if Util.MI.is_empty t.objectives ||
                 has_no_infinity t.objectives
                 (* otherwise, we may be unsound because infty optims
                    are not propagated *)
              then filt_choices
              else []
            in
            Debug.split_sat_contradicts_cs filt_choices;
            let t = reset_case_split_env t in
            look_for_sat ~for_model
              { t with choices = [] } [] filt_choices
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

  let extract_terms_from_choices =
    List.fold_left
      (fun acc (a, _, _, _, _) ->
         match a with
         | A.Eq(r1, r2) -> extract_from_semvalues acc [r1; r2]
         | A.Distinct (_, l) -> extract_from_semvalues acc l
         | A.Pred(p, _) -> extract_from_semvalues acc [p]
         | _ -> acc
      )

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
         (fun (a,ex,_dlvl,_plvl) ->
            CC_X.add_fact facts (LTerm a, ex, Th_util.Other))
      ) in_facts_l;

    let t, ch = try_it t facts ~for_model in
    let choices = extract_terms_from_choices SE.empty t.choices in
    let choices_terms = extract_terms_from_assumed choices ch in

    {t with terms = Expr.Set.union t.terms choices_terms}, choices_terms

  let do_case_split t origin =
    if Options.get_case_split_policy () == origin then
      do_case_split_aux t ~for_model:false
    else
      t, SE.empty

  let update_objectives objectives assumed gamma =
    let uf = CC_X.get_union_find gamma in
    let reset_cs_env = ref false in
    let res =
      List.fold_left
        (fun objectives (a, _, _) ->
           match E.term_view a with
           | {E.f = Sy.Op Sy.Optimize {order;is_max}; xs = [e]; _} ->
             let r =
               try Uf.make uf e
               with Not_found ->
                 (* gamma is already initialized with fresh terms *)
                 assert false
             in
             let x =
               Th_util.{
                 r;
                 e;
                 value = Unknown;
                 is_max;
                 order;
                 case_split = None
               } in
             begin
               try
                 let y = Util.MI.find order objectives in
                 if not (X.equal r y.Th_util.r) then begin
                   Printer.print_fmt ~flushed:true
                     (Options.Output.get_fmt_diagnostic ())
                     "Optimization problem illformed. %a and %a have \
                      the same order %d@."
                     X.print r X.print y.Th_util.r order;
                   assert false
                 end;
                 objectives
               with Not_found ->
                 reset_cs_env := true;
                 Util.MI.add order x objectives
             end
           | {E.f = Sy.Op Sy.Optimize _; xs = _; _} -> assert false
           | _ -> objectives
           (* | Not_a_term {is_lit = true} -> objectives
              | Not_a_term {is_lit = false} -> assert false *)
        ) objectives assumed
    in
    res, !reset_cs_env

  (* facts are sorted in decreasing order with respect to (dlvl, plvl) *)
  let assume ordered in_facts t =
    let facts = CC_X.empty_facts () in
    let assumed, assumed_set, cpt =
      List.fold_left
        (fun ((assumed, assumed_set, cpt) as accu) ((a, ex, dlvl, plvl)) ->
           if E.Set.mem a assumed_set
           then accu
           else
             begin
               CC_X.add_fact facts (LTerm a, ex, Th_util.Other);
               (a, dlvl, plvl) :: assumed,
               E.Set.add a assumed_set,
               cpt+1
             end
        )([], t.assumed_set, 0) in_facts
    in
    if assumed == [] then t, E.Set.empty, 0
    else
      let t = {t with assumed_set; assumed = assumed :: t.assumed;
                      cs_pending_facts = in_facts :: t.cs_pending_facts} in
      if Options.get_profiling() then Profiling.assume cpt;
      Debug.assumed t.assumed;
      assert (not ordered || is_ordered_list t.assumed);

      let gamma, _ = CC_X.assume_literals t.gamma [] facts in
      (* update to optimize with the new gamma *)
      let objectives, reset_cs_env =
        update_objectives t.objectives assumed gamma in
      let new_terms = CC_X.new_terms gamma in
      let t =  {t with
                gamma = gamma; terms = Expr.Set.union t.terms new_terms;
                objectives }
      in
      let t = if reset_cs_env then reset_case_split_env t else t in
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
        objectives = Util.MI.empty;
      }
    in
    let a = E.mk_distinct ~iff:false [E.vrai; E.faux] in
    let t, _, _ = assume true [a, Ex.empty, 0, -1] t in
    t

  let cl_extract env = CC_X.cl_extract env.gamma

  let assume ?(ordered=true) facts t =
    if Options.get_timers() then
      try
        Timers.exec_timer_start Timers.M_CC Timers.F_assume;
        let res = assume ordered facts t in
        Timers.exec_timer_pause Timers.M_CC Timers.F_assume;
        res
      with e ->
        Timers.exec_timer_pause Timers.M_CC Timers.F_assume;
        raise e
    else assume ordered facts t

  let query a t =
    if Options.get_timers() then
      try
        Timers.exec_timer_start Timers.M_CC Timers.F_query;
        let res = query a t in
        Timers.exec_timer_pause Timers.M_CC Timers.F_query;
        res
      with e ->
        Timers.exec_timer_pause Timers.M_CC Timers.F_query;
        raise e
    else query a t

  let extract_ground_terms env = env.terms

  let get_real_env t = t.gamma
  let get_case_split_env t = t.gamma_finite

  let compute_concrete_model env =
    let {gamma_finite; _}, _ =
      do_case_split_aux env ~for_model:true in
    CC_X.extract_concrete_model
      ~prop_model:env.assumed_set
      ~optimized_splits:env.objectives
      gamma_finite

  let assume_th_elt t th_elt dep =
    { t with gamma = CC_X.assume_th_elt t.gamma th_elt dep }

  let get_assumed env = env.assumed_set

  let reinit_cpt () =
    Debug.reinit_cpt ()

  let get_objectives env = env.objectives
end

module Main_Empty : S = struct

  type t =
    { assumed_set : E.Set.t }

  let empty () = { assumed_set = E.Set.empty }

  let assume ?ordered:(_=true) in_facts t =
    let assumed_set =
      List.fold_left
        (fun assumed_set ((a, _, _, _)) ->
           if E.Set.mem a assumed_set then assumed_set
           else E.Set.add a assumed_set
        ) t.assumed_set in_facts
    in
    {assumed_set}, E.Set.empty, 0

  let query _ _ = None

  let cl_extract _ = []
  let extract_ground_terms _ = Expr.Set.empty

  let get_real_env _ = CC_X.empty
  let get_case_split_env _ = CC_X.empty
  let do_case_split env _ = env, E.Set.empty
  let add_term env _ ~add_in_cs:_ = env
  let compute_concrete_model _env = None

  let assume_th_elt e _ _ = e
  let theories_instances ~do_syntactic_matching:_ _ e _ _ _ = e, []
  let get_assumed env = env.assumed_set

  let reinit_cpt () = ()

  let get_objectives _env = Util.MI.empty
end
