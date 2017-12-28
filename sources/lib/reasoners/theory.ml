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
(*     Copyright (C) 2013-2017 --- OCamlPro SAS                               *)
(*                                                                            *)
(*     This file is distributed under the terms of the Apache Software        *)
(*     License version 2.0                                                    *)
(*                                                                            *)
(******************************************************************************)

open Format
open Options
open Sig
open Exception

module X = Combine.Shostak
module Ex = Explanation
module T = Term
module A = Literal
module LR = A.Make(struct type t = X.r let compare = X.str_cmp include X end)
module SetT = Term.Set
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
    (Literal.LT.t * Explanation.t * int * int) list -> t ->
    t * Term.Set.t * int

  val query : Literal.LT.t -> t -> answer
  val class_of : t -> Term.t -> Term.t list
  val are_equal : t -> Term.t -> Term.t -> add_terms:bool -> Sig.answer
  val print_model : Format.formatter -> t -> unit
  val cl_extract : t -> Term.Set.t list
  val term_repr : t -> Term.t -> Term.t
  val extract_ground_terms : t -> Term.Set.t
  val get_real_env : t -> Ccx.Main.t
  val get_case_split_env : t -> Ccx.Main.t
  val do_case_split : t -> t * Term.Set.t
  val add_term : t -> Term.t -> add_in_cs:bool -> t
  val compute_concrete_model : t -> t


  val assume_th_elt : t -> Commands.th_elt -> t
  val theories_instances :
    do_syntactic_matching:bool ->
    Matching_types.info Term.Map.t * Term.t list Term.Map.t Term.Subst.t ->
    t -> (Formula.t -> Formula.t -> bool) ->
    int -> int -> t * Sig.instances

  val retrieve_used_context :
    t -> Explanation.t -> Formula.t list * Formula.t list

  val get_assumed : t -> Literal.LT.Set.t

end

module Main_Default : S = struct

  (*BISECT-IGNORE-BEGIN*)
  module Debug = struct

    let subterms_of_assumed l =
      List.fold_left
        (List.fold_left
           (fun st (a, _, _) -> Term.Set.union st (A.LT.terms_rec a))
        )SetT.empty l

    let types_of_subterms st =
      SetT.fold (fun t acc -> Ty.Set.add (T.type_info t) acc) st Ty.Set.empty

    let generalize_types ty1 ty2 = match ty1, ty2 with
      | Ty.Tvar _, _ -> ty1
      | _, Ty.Tvar _ -> ty2
      | _ -> Ty.fresh_tvar ()

    let logics_of_assumed st =
      SetT.fold
        (fun t mp ->
          match T.view t with
          | {T.f = Sy.Name (hs, ((Sy.Ac | Sy.Other) as is_ac)); xs=xs; ty=ty} ->
            let xs = List.map T.type_info xs in
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
        )st Hstring.Map.empty

    let types_of_assumed sty =
      let open Ty in
      Ty.Set.fold
        (fun ty mp ->
          match ty with
          | Tint | Treal | Tbool | Tunit | Tbitv _ | Tfarray _ -> mp
          | Tvar _ | Tnext _ -> assert false

          | Text (_, hs) | Tsum (hs, _) | Trecord {name=hs} when
              Hstring.Map.mem hs mp -> mp

          | Text (l, hs) ->
            let l = List.map (fun _ -> Ty.fresh_tvar()) l in
            Hstring.Map.add hs (Text(l, hs)) mp

          | Tsum (hs, l) ->
            Hstring.Map.add hs (Tsum(hs, l)) mp

          | Trecord {args; name; lbs} ->
            (* cannot do better for records ? *)
            Hstring.Map.add name ty mp
        )sty Hstring.Map.empty

    let print_types_decls types =
      let open Ty in
      Hstring.Map.iter
        (fun _ ty ->
          match ty with
          | Tint | Treal | Tbool | Tunit | Tbitv _ | Tfarray _ -> ()
          | Tvar _ | Tnext _ -> assert false
          | Text _ -> fprintf fmt "@.type %a@." Ty.print ty
          | Tsum (_, l) ->
            fprintf fmt "@.type %a = " Ty.print ty;
            begin match l with
            | [] -> assert false
            | e::l ->
              fprintf fmt "%s" (Hstring.view e);
              List.iter (fun e -> fprintf fmt " | %s" (Hstring.view e)) l;
              fprintf fmt "@."
            end

          | Trecord {Ty.lbs} ->
            fprintf fmt "@.type %a = " Ty.print ty;
            begin match lbs with
            | [] -> assert false
            | (lbl, ty)::l ->
              fprintf fmt "{ %s : %a" (Hstring.view lbl) Ty.print ty;
              List.iter
                (fun (lbl, ty) ->
                  fprintf fmt " ; %s : %a" (Hstring.view lbl) Ty.print ty) l;
              fprintf fmt " }@."
            end
        )types;
      fprintf fmt "@."

    let print_arrow_type fmt xs =
      match xs with
      | [] -> ()
      | e :: l ->
        fprintf fmt "%a" Ty.print e;
        List.iter (fprintf fmt ", %a" Ty.print) l;
        fprintf fmt " -> "

    let print_logics logics =
      Hstring.Map.iter
        (fun hs (xs, ty, is_ac) ->
          fprintf fmt "logic %s%s : %a%a@.@."
            (if is_ac == Sy.Ac then "ac " else "")
            (Hstring.view hs)
            print_arrow_type xs
            Ty.print ty
        )logics

    let print_declarations l =
      let st = subterms_of_assumed l in
      let sty = types_of_subterms st in
      let types = types_of_assumed sty in
      let logics = logics_of_assumed st in
      print_types_decls types;
      print_logics logics

    let assumed =
      let cpt = ref 0 in
      fun l ->
        if debug_cc () then begin
          fprintf fmt "[cc] Assumed facts (in this order):@.@.";
          print_declarations l;
          incr cpt;
          fprintf fmt "@.goal g_%d :@." !cpt;
          List.iter
            (fun l ->
              fprintf fmt "@.(*call to assume*)@.";
              match List.rev l with
              | [] -> assert false
              | (a,dlvl,plvl)::l ->
                fprintf fmt "( (* %d , %d *) %a " dlvl plvl
                  Literal.LT.print a;
                List.iter
                  (fun (a, dlvl, plvl) ->
                    fprintf fmt " and@. (* %d , %d *) %a " dlvl plvl
                      Literal.LT.print a
                  ) l;
                fprintf fmt " ) ->@."
            ) (List.rev l);
          fprintf fmt "false@.";
        end

    let theory_of k = match k with
      | Th_arith  -> "Th_arith "
      | Th_sum    -> "Th_sum   "
      | Th_arrays -> "Th_arrays"
      | Th_UF -> "Th_UF"

    let made_choices fmt choices =
      match choices with
      | [] -> ()
      | _ ->
        fprintf fmt "Stack of choices:@.";
        List.iter
          (fun (rx, lit_orig, _, ex) ->
            match lit_orig with
            | CS(k, sz) ->
              fprintf fmt "  > %s  cs: %a (because %a)@."
                (theory_of k) LR.print (LR.make rx) Ex.print ex
            | NCS(k, sz) ->
              fprintf fmt "  > %s ncs: %a (because %a)@."
                (theory_of k) LR.print (LR.make rx) Ex.print ex
            | _ -> assert false
          )choices;
        fprintf fmt "==============================================@."

    let begin_case_split choices =
      if debug_split () then
	fprintf fmt "============= Begin CASE-SPLIT ===============@.%a@."
          made_choices choices

    let end_case_split choices =
      if debug_split () then
	fprintf fmt "============= End CASE-SPLIT =================@.%a@."
          made_choices choices

    let split_size sz =
      if debug_split () then
	fprintf fmt ">size case-split: %s@." (Numbers.Q.to_string sz)

    let print_lr_view fmt ch = LR.print fmt (LR.make ch)

    let split_backtrack neg_c ex_c =
      if debug_split () then
        fprintf fmt "[case-split] I backtrack on %a : %a@."
          print_lr_view neg_c Ex.print ex_c

    let split_assume c ex_c =
      if debug_split () then
        fprintf fmt "[case-split] I assume %a : %a@."
          print_lr_view c Ex.print ex_c

    let split_backjump c dep =
      if debug_split () then
        fprintf fmt "[case-split] I backjump on %a : %a@."
          print_lr_view c Ex.print dep

    let query a =
      if debug_cc () then fprintf fmt "[cc] query : %a@." A.LT.print a

    let split_sat_contradicts_cs filt_choices =
      if debug_split () then
        fprintf fmt
          "[case-split] The SAT contradicts CS! I'll replay choices@.%a@."
          made_choices filt_choices

  end
  (*BISECT-IGNORE-END*)

  type choice_sign =
    | CPos of Ex.exp (* The explication of this choice *)
    | CNeg (* The choice has been already negated *)


  type t = {
    assumed_set : Literal.LT.Set.t;
    assumed : (Literal.LT.t * int * int) list list;
    cs_pending_facts : (Literal.LT.t * Ex.t * int * int) list list;
    terms : Term.Set.t;
    gamma : CC_X.t;
    gamma_finite : CC_X.t;
    choices : (X.r Literal.view * lit_origin * choice_sign * Ex.t) list;
  (** the choice, the size, choice_sign,  the explication set,
      the explication for this choice. *)
  }

  let look_for_sat ?(bad_last=No) ch t base_env l ~for_model =
    let rec aux ch bad_last dl base_env li =
      Options.exec_thread_yield ();
      match li, bad_last with
        | [], _ ->
	  begin
	    Options.tool_req 3 "TR-CCX-CS-Case-Split";
            let l, base_env = CC_X.case_split base_env for_model in
            match l with
	      | [] ->
		{ t with gamma_finite = base_env; choices = List.rev dl }, ch
	      | l ->
	        let l =
		  List.map
		    (fun (c, is_cs, size) ->
                      Options.incr_cs_steps();
                      let exp = Ex.fresh_exp () in
                      let ex_c_exp =
                        if is_cs then Ex.add_fresh exp Ex.empty else Ex.empty
                      in
                      (* A new explanation in order to track the choice *)
                      (c, size, CPos exp, ex_c_exp)) l in
		  aux ch No dl base_env l
	  end
        | ((c, lit_orig, CNeg, ex_c) as a)::l, _ ->
          let facts = CC_X.empty_facts () in
          CC_X.add_fact facts (LSem c,ex_c,lit_orig);
	  let base_env, ch = CC_X.assume_literals base_env ch facts in
	  aux ch bad_last (a::dl) base_env l

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
	    let base_env, ch =  CC_X.assume_literals base_env ch facts in
	    Options.tool_req 3 "TR-CCX-CS-Normal-Run";
	    aux ch bad_last (a::dl) base_env l
	  with Exception.Inconsistent (dep, classes) ->
            match Ex.remove_fresh exp dep with
              | None ->
                (* The choice doesn't participate to the inconsistency *)
                Debug.split_backjump c dep;
		Options.tool_req 3 "TR-CCX-CS-Case-Split-Conflict";
                raise (Exception.Inconsistent (dep, classes))
              | Some dep ->
		Options.tool_req 3 "TR-CCX-CS-Case-Split-Progress";
                (* The choice participates to the inconsistency *)
                let neg_c = LR.view (LR.neg (LR.make c)) in
                let lit_orig = match lit_orig with
                  | CS(k, sz) -> NCS(k, sz)
                  | _ -> assert false
                in
	        Debug.split_backtrack neg_c dep;
		if bottom_classes () then
		  printf "bottom (case-split):%a\n@."
		    Term.print_tagged_classes classes;
		aux ch No dl base_env [neg_c, lit_orig, CNeg, dep]
    in
    aux ch bad_last (List.rev t.choices) base_env l

  (* remove old choices involving fresh variables that are no longer in UF *)
  let filter_choice uf (ra,_,_,_) =
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
            | Some t, _ -> Combine.Uf.mem uf t
            | _ -> true
          )(X.leaves r)
      )l


  let try_it t facts ~for_model =
    Options.exec_thread_yield ();
    Debug.begin_case_split t.choices;
    let r =
      try
	if t.choices == [] then look_for_sat [] t t.gamma [] for_model
	else
	  try
	    let env, ch = CC_X.assume_literals t.gamma_finite [] facts in
	    look_for_sat ch t env [] for_model
	  with Exception.Inconsistent (dep, classes) ->
	    Options.tool_req 3 "TR-CCX-CS-Case-Split-Erase-Choices";
	    (* we replay the conflict in look_for_sat, so we can
	       safely ignore the explanation which is not useful *)
            let uf =  CC_X.get_union_find t.gamma in
            let filt_choices = List.filter (filter_choice uf) t.choices in
            Debug.split_sat_contradicts_cs filt_choices;
	    look_for_sat ~bad_last:(Yes (dep, classes))
	      [] { t with choices = []} t.gamma filt_choices ~for_model
      with Exception.Inconsistent (d, cl) ->
	Debug.end_case_split t.choices;
	Options.tool_req 3 "TR-CCX-CS-Conflict";
	raise (Exception.Inconsistent (d, cl))
    in
    Debug.end_case_split (fst r).choices; r


  let extract_from_semvalues acc l =
    List.fold_left
      (fun acc r ->
	match X.term_extract r with
	  | Some t, _ -> SetT.add t acc | _ -> acc) acc l

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
      (fun acc (a, _, _) ->
	match a with
	  | LTerm r -> begin
	    match Literal.LT.view r with
	      | Literal.Eq (t1, t2) ->
		SetT.add t1 (SetT.add t2 acc)
	      | Literal.Distinct (_, l) | Literal.Builtin (_, _, l) ->
		List.fold_right SetT.add l acc
	      | Literal.Pred (t1, _) ->
		SetT.add t1 acc

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

  let do_case_split t =
    let in_facts_l = t.cs_pending_facts in
    let t = {t with cs_pending_facts = []} in
    let facts = CC_X.empty_facts () in
    List.iter
      (List.iter
         (fun (a,ex,dlvl,plvl) -> CC_X.add_fact facts (LTerm a, ex, Sig.Other))
      ) in_facts_l;

    let t, ch = try_it t facts ~for_model:false in
    let choices = extract_terms_from_choices SetT.empty t.choices in
    let choices_terms = extract_terms_from_assumed choices ch in

    {t with terms = Term.Set.union t.terms choices_terms}, choices_terms

  (* facts are sorted in decreasing order with respect to (dlvl, plvl) *)
  let assume ordered in_facts t =
    let facts = CC_X.empty_facts () in
    let assumed, assumed_set, cpt =
      List.fold_left
        (fun ((assumed, assumed_set, cpt) as accu) ((a, ex, dlvl, plvl)) ->
          if Literal.LT.Set.mem a assumed_set
          then accu
          else
            begin
              CC_X.add_fact facts (LTerm a, ex, Sig.Other);
              (a, dlvl, plvl) :: assumed,
              Literal.LT.Set.add a assumed_set,
              cpt+1
            end
        )([], t.assumed_set, 0) in_facts
    in
    let t = {t with assumed_set; assumed = assumed :: t.assumed;
                    cs_pending_facts = in_facts :: t.cs_pending_facts} in
    if Options.profiling() then Profiling.assume cpt;
    Debug.assumed t.assumed;
    assert (not ordered || is_ordered_list t.assumed);

    let gamma, ch = CC_X.assume_literals t.gamma [] facts in
    let new_terms = CC_X.new_terms gamma in
    {t with gamma = gamma; terms = Term.Set.union t.terms new_terms},
    new_terms, cpt

  let class_of t term = CC_X.class_of t.gamma term

  let debug_theories_instances th_instances ilvl dlvl =
    let module MF = Formula.Map in
    fprintf fmt "===========================================================@.";
    fprintf fmt
      "[Theory] dec. level = %d, instant. level = %d, %d new Th instances@."
      dlvl ilvl (List.length th_instances);
    let mp =
      List.fold_left
        (fun acc ((hyps:Formula.t list),gf, _) ->
          match gf.Formula.lem with
          | None -> assert false
          | Some lem ->
            let inst =
              try MF.find lem acc with Not_found -> MF.empty
            in
            MF.add lem (MF.add gf.Formula.f hyps inst) acc
        )MF.empty th_instances
    in
    let l =
      MF.fold
        (fun f inst acc -> (f, MF.cardinal inst, inst) :: acc) mp []
    in
    let l = List.fast_sort (fun (_,m,_) (_,n,_) -> n - m) l in
    List.iter (fun (f, m, inst) ->
      fprintf fmt "@.%3d  -->  %a@." m Formula.print f;
      if true then begin
        MF.iter
          (fun f hyps ->
            fprintf fmt "  [inst]@.";
            List.iter
              (fun h ->
                fprintf fmt "    hypothesis: %a@." Formula.print h;
              )hyps;
            fprintf fmt "    conclusion: %a@." Formula.print f;
          ) inst;
      end
    ) l

 let theories_instances ~do_syntactic_matching t_match t selector dlvl ilvl =
   let gamma, instances =
     CC_X.theories_instances ~do_syntactic_matching t_match t.gamma selector in
   if debug_fpa() > 0 then debug_theories_instances instances dlvl ilvl;
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
    if Options.profiling() then Profiling.query();
    Options.exec_thread_yield ();
    Debug.query a;
    try
      match A.LT.view a with
      | A.Eq (t1, t2)  ->
	 let t = add_and_process_conseqs a t in
         CC_X.are_equal t.gamma t1 t2 ~added_terms:true

      | A.Distinct (false, [t1; t2]) ->
	 let na = A.LT.neg a in
	 let t = add_and_process_conseqs na t in (* na ? *)
	 CC_X.are_distinct t.gamma t1 t2

      | A.Distinct _ ->
	 assert false (* devrait etre capture par une analyse statique *)

      | A.Pred (t1,b) ->
	 let t = add_and_process_conseqs a t in
         if b
         then CC_X.are_distinct t.gamma t1 (Term.top())
         else CC_X.are_equal t.gamma t1 (Term.top()) ~added_terms:true

      | _ ->
	 let na = A.LT.neg a in
	 let t = add_and_process_conseqs na t in
         CC_X.query t.gamma na
    with Exception.Inconsistent (d, classes) ->
      Yes (d, classes)

  let are_equal t t1 t2 add_terms =
    if add_terms then
      let facts = CC_X.empty_facts() in
      let gamma, facts = CC_X.add_term t.gamma facts t1 Ex.empty in
      let gamma, facts = CC_X.add_term gamma facts t2 Ex.empty in
      try
        let gamma, _ = CC_X.assume_literals gamma [] facts in
        CC_X.are_equal gamma t1 t2 ~added_terms:true
      with Inconsistent (ex,cl) -> Yes(ex, cl)
    else
      CC_X.are_equal t.gamma t1 t2 ~added_terms:false

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
    let env, _ = CC_X.add_term env (CC_X.empty_facts()) T.vrai Ex.empty in
    let env, _ = CC_X.add_term env (CC_X.empty_facts()) T.faux Ex.empty in
    let t =
      { gamma = env;
        gamma_finite = env;
        choices = [];
        assumed_set = Literal.LT.Set.empty;
        assumed = [];
        cs_pending_facts = [];
        terms = Term.Set.empty }
    in
    let a = A.LT.mk_distinct false [T.vrai; T.faux] in
    let t, _, _ = assume true [a, Ex.empty, 0, -1] t in
    t

  let print_model fmt t = CC_X.print_model fmt t.gamma_finite

  let cl_extract env = CC_X.cl_extract env.gamma

  let term_repr env t = CC_X.term_repr env.gamma t

  let assume ?(ordered=true) facts t =
    if Options.timers() then
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
    if Options.timers() then
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


  let are_equal env t1 t2 ~add_terms =
    if Options.timers() then
      try
	Timers.exec_timer_start Timers.M_CC Timers.F_are_equal;
	let res = are_equal env t1 t2 add_terms in
	Timers.exec_timer_pause Timers.M_CC Timers.F_are_equal;
	res
      with e ->
	Timers.exec_timer_pause Timers.M_CC Timers.F_are_equal;
	raise e
    else are_equal env t1 t2 add_terms

  let compute_concrete_model env =
    fst (try_it env (CC_X.empty_facts ()) ~for_model:true)


  let assume_th_elt t th_elt =
    { t with gamma = CC_X.assume_th_elt t.gamma th_elt }

  let retrieve_used_context env dep =
    CC_X.retrieve_used_context env.gamma dep

  let get_assumed env = env.assumed_set

end

module Main_Empty : S = struct

  type t =
    { assumed_set : Literal.LT.Set.t }

  let empty () = { assumed_set = Literal.LT.Set.empty }

  let assume ?(ordered=true) in_facts t =
    let assumed_set =
      List.fold_left
        (fun assumed_set ((a, ex, dlvl, plvl)) ->
          if Literal.LT.Set.mem a assumed_set then assumed_set
          else Literal.LT.Set.add a assumed_set
        ) t.assumed_set in_facts
    in
    {assumed_set}, T.Set.empty, 0

  let query a t = No
  let class_of env t = [t]
  let are_equal env t1 t2 ~add_terms =
    if T.equal t1 t2 then Yes(Ex.empty, []) else No
  let print_model _ _ = ()
  let cl_extract _ = []
  let term_repr _ t = t
  let extract_ground_terms _ = Term.Set.empty

  let empty_ccx = CC_X.empty ()
  let get_real_env _ = empty_ccx
  let get_case_split_env _ = empty_ccx
  let do_case_split env = env, T.Set.empty
  let add_term env t ~add_in_cs = env
  let compute_concrete_model e = e
  let terms_in_repr e = Term.Set.empty

  let assume_th_elt e _ = e
  let theories_instances ~do_syntactic_matching _ e _ _ _ = e, []
  let retrieve_used_context _ _ = [], []
  let get_assumed env = env.assumed_set
end

module Main =
  (val
      (
        if Options.no_theory() then (module Main_Empty : S)
        else (module Main_Default : S)
      ) : S
  )
