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
  val compute_concrete_model : t -> t

  val assume_th_elt : t -> Expr.th_elt -> Explanation.t -> t
  val theories_instances :
    do_syntactic_matching:bool ->
    Matching_types.info Expr.Map.t * Expr.t list Expr.Map.t Symbols.Map.t ->
    t -> (Expr.t -> Expr.t -> bool) ->
    int -> int -> t * Sig_rel.instances

  val get_assumed : t -> E.Set.t

  val output_concrete_model :
    Format.formatter ->
    prop_model:Expr.Set.t ->
    t ->
    unit

  val reinit_cpt : unit -> unit

end

module Main_Default : S = struct

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

    let theory_of k = match k with
      | Th_util.Th_arith  -> "Th_arith "
      | Th_util.Th_sum    -> "Th_sum   "
      | Th_util.Th_adt    -> "Th_adt   "
      | Th_util.Th_arrays -> "Th_arrays"
      | Th_util.Th_UF -> "Th_UF"

    let made_choices fmt choices =
      match choices with
      | [] -> ()
      | _ ->
        Format.fprintf fmt "@[<v 2>Stack of choices:@ ";
        List.iter
          (fun (rx, lit_orig, _, ex) ->
             match lit_orig with
             | Th_util.CS(k, _) ->
               Format.fprintf fmt "  > %s  cs: %a (because %a)@ "
                 (theory_of k) LR.print (LR.make rx) Ex.print ex
             | Th_util.NCS(k, _) ->
               Format.fprintf fmt "  > %s ncs: %a (because %a)@ "
                 (theory_of k) LR.print (LR.make rx) Ex.print ex
             | _ -> assert false
          )choices;
        Format.fprintf fmt "==============================================@."

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

  type choice_sign =
    | CPos of Ex.exp (* The explication of this choice *)
    | CNeg (* The choice has been already negated *)


  type choice =
    X.r Xliteral.view * Th_util.lit_origin * choice_sign * Ex.t
  (** the choice, the size, choice_sign,  the explication set,
        the explication for this choice. *)

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

  let add_explanations_to_splits l =
    List.map
      (fun (c, is_cs, size) ->
         Steps.incr_cs_steps();
         let exp = Ex.fresh_exp () in
         let ex_c_exp =
           if is_cs then Ex.add_fresh exp Ex.empty else Ex.empty
         in
         (* A new explanation in order to track the choice *)
         (c, size, CPos exp, ex_c_exp)) l

  let register_optimized_split objectives u =
    try
      let x = Util.MI.find u.Th_util.order objectives in
      assert (E.equal x.Th_util.e u.Th_util.e); (* and its Value ... *)
      Util.MI.add u.Th_util.order u objectives
    with Not_found ->
      assert false


  exception Found of Th_util.optimized_split

  let next_optimization env ~for_model =
    try
      Util.MI.iter (fun _ x ->
          match x.Th_util.value with
          | Value _ ->
            ()
          | Pinfinity | Minfinity ->
            (* We should block case-split at infinite values.
               Otherwise. Otherwise, we may have soundness issues. We
               may think an objective is unbounded, but some late
               constraints may make it bounded.

               An alternative is to only allow further splits when we
               know that no extra-assumpptions will be propagated to
               the env. Hence the test 'if for_model' *)
            if for_model then ()
            else
              raise (Found { x with Th_util.value = Unknown })

          | Unknown ->
            raise (Found { x with Th_util.value = Unknown })
        )env.objectives;
      None
    with Found x ->
      Some x

  let look_for_sat ?(bad_last=None) ch env l ~for_model =
    let rec aux ch bad_last dl env li =
      Options.exec_thread_yield ();
      match li, bad_last with
      | [], _ ->
        begin
          Options.tool_req 3 "TR-CCX-CS-Case-Split";
          let to_optimize = next_optimization ~for_model env in
          let l, base_env = CC_X.case_split
              env.gamma_finite ~for_model ~to_optimize in
          let env = {env with gamma_finite = base_env} in
          match l with
          | Sig_rel.Split [] ->
            { env with choices = List.rev dl }, ch

          | Sig_rel.Split new_splits ->
            let new_splits = add_explanations_to_splits new_splits in
            aux ch None dl env new_splits

          | Sig_rel.Optimized_split u ->
            let to_opt = register_optimized_split env.objectives u in
            let env = {env with objectives = to_opt} in
            begin
              match u.value with
              | Value v ->
                let splits = add_explanations_to_splits [v] in
                aux ch None dl env splits
              | Pinfinity | Minfinity ->
                if for_model then
                  aux ch None dl env []
                else
                  { env with choices = List.rev dl }, ch
              | Unknown -> assert false
            end

        end
      | ((c, lit_orig, CNeg, ex_c) as a)::l, _ ->
        let facts = CC_X.empty_facts () in
        CC_X.add_fact facts (LSem c,ex_c,lit_orig);
        let base_env, ch = CC_X.assume_literals env.gamma_finite ch facts in
        let env = { env with gamma_finite = base_env} in
        aux ch bad_last (a::dl) env l

      (* This optimisation is not correct with the current explanation *)
      (* | [(c, lit_orig, CPos exp, ex_c)], Yes (dep,_) -> *)
      (*     let neg_c = CC_X.Rel.choice_mk_not c in *)
      (*     let ex_c = Ex.union ex_c dep in *)
      (*     Debug.split_backtrack neg_c ex_c; *)
      (*     aux ch No dl base_env [neg_c, Numbers.Q.Int 1, CNeg, ex_c] *)

      | ((c, lit_orig, CPos exp, ex_c_exp) as a)::l, _ ->
        try
          Debug.split_assume c ex_c_exp;
          let facts = CC_X.empty_facts () in
          CC_X.add_fact facts (LSem c, ex_c_exp, lit_orig);
          let base_env, ch =  CC_X.assume_literals env.gamma_finite ch facts in
          let env = { env with gamma_finite = base_env} in
          Options.tool_req 3 "TR-CCX-CS-Normal-Run";
          aux ch bad_last (a::dl) env l
        with Ex.Inconsistent (dep, classes) ->
        match Ex.remove_fresh exp dep with
        | None ->
          (* The choice doesn't participate to the inconsistency *)
          Debug.split_backjump c dep;
          Options.tool_req 3 "TR-CCX-CS-Case-Split-Conflict";
          raise (Ex.Inconsistent (dep, classes))
        | Some dep ->
          Options.tool_req 3 "TR-CCX-CS-Case-Split-Progress";
          (* The choice participates to the inconsistency *)
          let neg_c = LR.view (LR.neg (LR.make c)) in
          let lit_orig = match lit_orig with
            | Th_util.CS(k, sz) -> Th_util.NCS(k, sz)
            | _ -> assert false
          in
          Debug.split_backtrack neg_c dep;
          if Options.get_bottom_classes () then
            Printer.print_dbg
              "bottom (case-split):%a"
              Expr.print_tagged_classes classes;
          aux ch None dl env [neg_c, lit_orig, CNeg, dep]
    in
    aux ch bad_last (List.rev env.choices) env l

  (* remove old choices involving fresh variables that are no longer in UF *)
  let filter_valid_choice uf (ra,_,_,_) =
    let l = match ra with
      | A.Eq(r1, r2) -> [r1; r2]
      | A.Distinct (_, l) -> l
      | A.Builtin (_,_, l) -> l
      | A.Pred(p, _) -> [p]
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
        )Ex.empty to_ignore
    in
    List.filter
      (fun (_,_,_,ex) ->
         try
           Ex.iter_atoms
             (function
               | Ex.Fresh _ as fr when Ex.mem fr ignored_decisions -> raise Exit
               | _ -> ()
             )ex;
           true
         with Exit -> (* ignore implicated related to ignored decisions *)
           false
      )candidates_to_keep


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

  let try_it t facts ~for_model =
    Options.exec_thread_yield ();
    Debug.begin_case_split t.choices;
    let r =
      try
        if t.choices == [] then
          (* no splits yet: init gamma_finite with gamma *)
          let t = reset_case_split_env t in
          look_for_sat [] t [] ~for_model
        else
          try
            let base_env, ch = CC_X.assume_literals t.gamma_finite [] facts in
            let t = { t with gamma_finite = base_env } in
            look_for_sat ch t [] ~for_model
          with Ex.Inconsistent (dep, classes) ->
            Options.tool_req 3 "TR-CCX-CS-Case-Split-Erase-Choices";
            (* we replay the conflict in look_for_sat, so we can
               safely ignore the explanation which is not useful *)
            let uf =  CC_X.get_union_find t.gamma in
            let filt_choices = filter_choices uf t.choices in
            Debug.split_sat_contradicts_cs filt_choices;
            (* re-init gamma_finite with gamma *)
            let t = reset_case_split_env t in
            look_for_sat ~bad_last:(Some (dep, classes))
              [] { t with choices = []} filt_choices ~for_model
      with Ex.Inconsistent (d, cl) ->
        Debug.end_case_split t.choices;
        Options.tool_req 3 "TR-CCX-CS-Conflict";
        raise (Ex.Inconsistent (d, cl))
    in
    Debug.end_case_split (fst r).choices; r


  let extract_from_semvalues acc l =
    List.fold_left
      (fun acc r ->
         match X.term_extract r with
         | Some t, _ -> SE.add t acc | _ -> acc) acc l

  let extract_terms_from_choices =
    List.fold_left
      (fun acc (a, _, _, _) ->
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
      let new_terms = CC_X.new_terms gamma in
      {t with gamma = gamma; terms = Expr.Set.union t.terms new_terms},
      new_terms, cpt

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
    let env = CC_X.empty () in
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
    fst @@ do_case_split_aux env ~for_model:true


  let assume_th_elt t th_elt dep =
    { t with gamma = CC_X.assume_th_elt t.gamma th_elt dep }

  let get_assumed env = env.assumed_set

  let output_concrete_model fmt ~prop_model env =
    CC_X.output_concrete_model fmt ~prop_model env.gamma_finite

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
        (fun assumed_set ((a, _, _, _)) ->
           if E.Set.mem a assumed_set then assumed_set
           else E.Set.add a assumed_set
        ) t.assumed_set in_facts
    in
    {assumed_set}, E.Set.empty, 0

  let query _ _ = None

  let cl_extract _ = []
  let extract_ground_terms _ = Expr.Set.empty

  let empty_ccx = CC_X.empty ()
  let get_real_env _ = empty_ccx
  let get_case_split_env _ = empty_ccx
  let do_case_split env _ = env, E.Set.empty
  let add_term env _ ~add_in_cs:_ = env
  let compute_concrete_model e = e

  let assume_th_elt e _ _ = e
  let theories_instances ~do_syntactic_matching:_ _ e _ _ _ = e, []
  let get_assumed env = env.assumed_set
  let output_concrete_model _fmt ~prop_model:_ _env = ()
  let reinit_cpt () = ()
end
