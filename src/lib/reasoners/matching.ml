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

module Sy = Symbols
module E = Expr
module ME = E.Map

type subst = {
  content : Expr.Subst.t;
  age : int;
  lemma_orig : Expr.t;
  terms_orig : Expr.t list;
  from_goal : bool;
}

type term_info = {
  age : int;
  lemmas_orig : Expr.t list;
  terms_orig : Expr.t list;
  from_goal : bool;
}

type trigger_info = {
  age : int;
  lemma_orig : Expr.t;
  formula_orig : Expr.t;
  dep : Explanation.t;
  increm_guard : Expr.t;
}

type env = {
  fils : Expr.Set.t Symbols.Map.t;
  (* Map of symbols to the known terms having this symbol as top symbol. *)

  known_terms : term_info Expr.Map.t;
  (* Map of the known terms to their information. *)

  known_triggers : trigger_info Expr.Trigger.Map.t;
  (* Map of the known triggers to their information. *)

  max_t_depth : int;
  (* The current maximal depth. This field is used to limit the size of
     the environment. *)
}

module type S = sig
  type t = env
  type theory

  val make : int -> t

  val clean_triggers : t -> t

  val add_term :
    t ->
    age:int ->
    from_goal:bool ->
    ?lemma_orig:Expr.t ->
    terms_orig:Expr.t list ->
    Expr.t ->
    t

  val max_term_depth : t -> int -> t

  val add_triggers :
    Util.matching_env ->
    (int * Expr.t * Explanation.t) Expr.Map.t ->
    t ->
    t

  val query :
    Util.matching_env ->
    t ->
    theory ->
    (Expr.trigger * trigger_info * subst list) list
end

module type Arg = sig
  type t

  val term_repr : t -> E.t -> init_term:bool -> E.t
  val are_equal : t -> E.t -> E.t -> init_terms:bool -> Th_util.answer
  val class_of : t -> E.t -> E.t list
end

module Make (X : Arg) : S with type theory = X.t = struct

  type theory = X.t

  type t = env

  exception Echec

  let[@inline always] make max_t_depth = {
    fils = Symbols.Map.empty;
    known_terms = Expr.Map.empty;
    known_triggers = Expr.Trigger.Map.empty;
    max_t_depth;
  }

  let clean_triggers env = { env with known_triggers = Expr.Trigger.Map.empty }

  (*BISECT-IGNORE-BEGIN*)
  module Debug = struct
    open Printer
    let add_term t =
      if get_debug_matching() >= 3 then
        print_dbg
          ~module_name:"Matching" ~function_name:"add_term"
          "add_term:  %a" E.print t

    let matching tr =
      if get_debug_matching() >= 3 then
        print_dbg
          ~module_name:"Matching" ~function_name:"matching"
          "@[<v 0>(multi-)trigger: %a@ \
           ========================================================@]"
          E.print_list tr.E.content

    let match_pat_modulo pat sbts =
      if get_debug_matching() >= 3 then
        let print fmt sbt =
          fprintf fmt ">>> sbs= %a@ " Expr.Subst.pp sbt.content
        in
        print_dbg
          ~module_name:"Matching" ~function_name:"match_pat_modulo"
          "@[<v 2>match_pat_modulo: %a  with accumulated substs@ %a@]"
          E.print pat (pp_list_no_space print) sbts

    let match_one_pat sbt pat0 =
      if get_debug_matching() >= 3 then
        print_dbg
          ~module_name:"Matching" ~function_name:"match_one_pat"
          "match_pat: %a with subst: %a"
          E.print pat0 Expr.Subst.pp sbt.content


    let match_one_pat_against sbt pat0 t =
      if get_debug_matching() >= 3 then
        print_dbg
          ~module_name:"Matching" ~function_name:"match_one_pat_against"
          "@[<v 0>match_pat: %a against term %a@ \
           with subst: %a@]"
          E.print pat0
          E.print t
          Expr.Subst.pp sbt.content

    let match_term sbt t pat =
      if get_debug_matching() >= 3 then
        print_dbg
          ~module_name:"Matching" ~function_name:"match_term"
          "I match %a against %a with subst: %a"
          E.print pat E.print t Expr.Subst.pp sbt.content

    let match_list sbt pats terms =
      if get_debug_matching() >= 3 then
        print_dbg
          ~module_name:"Matching" ~function_name:"match_list"
          "I match %a against %a with subst: %a"
          E.print_list pats
          E.print_list terms
          Expr.Subst.pp sbt.content

    let match_class_of t cl =
      if get_debug_matching() >= 3 then
        print_dbg
          ~module_name:"Matching" ~function_name:"match_class_of"
          "class_of (%a) = { %a }"
          E.print t
          (fun fmt -> List.iter (fprintf fmt "%a , " E.print)) cl

    let candidate_substitutions tr tr_info res =
      if get_debug_matching () >= 1 then
        print_dbg
          ~module_name:"Matching" ~function_name:"candidate_substitutions"
          "@[<v 2>%3d candidate substitutions for Axiom %a with trigger %a@ "
          (List.length res)
          E.print tr_info.lemma_orig
          E.print_list tr.E.content;
      if get_debug_matching() >= 2 then
        List.iter
          (fun { content; _ } ->
             print_dbg ~header:false ">>> %a@ " Expr.Subst.pp content
          ) res

  end
  (*BISECT-IGNORE-END*)

  let add_term env ~age ~from_goal ?lemma_orig ~terms_orig t =
    Debug.add_term t;
    let rec add_rec env t =
      if Expr.Map.mem t env.known_terms then env
      else begin
        let env =
          (* Retrieve all the known terms whose the top symbol is f. *)
          let map_f =
            try Symbols.Map.find t.f env.fils with Not_found -> Expr.Set.empty
          in
          let fils = Symbols.Map.add t.f (Expr.Set.add t map_f) env.fils in
          let lemmas_orig =
            match lemma_orig with
            | Some lem -> [lem]
            | None -> []
          in
          let info = { age; from_goal; lemmas_orig; terms_orig } in
          let known_terms = Expr.Map.add t info env.known_terms in
          { env with fils; known_terms }
        in
        (* Recursively adding the subterms of the term t. *)
        List.fold_left add_rec env t.xs
      end
    in
    (* Too old terms are ignored by the matching. *)
    if age > Options.get_age_bound () then env else add_rec env t

  (* Map of equalities between terms used as a cache. *)
  module MT2 = Map.Make(struct
      type t = E.t * E.t
      let compare (a, b) (x, y) =
        let c = E.compare a x in if c <> 0 then c else E.compare b y
    end)

  let are_equal, reset_cache_refs =
    (* These references are reset before and after each call to query.
       If some intermediate functions are exported in the future, the code
       should be adapted. *)
    let cache_light = ref MT2.empty in
    let cache_full  = ref MT2.empty in
    (fun tbox t s ~(mode: [`Light | `Full ]) ->
       let cache, init_terms =
         match mode with
         | `Light -> cache_light, false
         | `Full  -> cache_full,  true
       in
       try MT2.find (t, s) !cache
       with Not_found ->
         let res = X.are_equal tbox t s ~init_terms |> Option.is_some in
         cache := MT2.add (t, s) res (MT2.add (s, t) res !cache);
         res
    ),
    (fun () ->
       cache_light := MT2.empty;
       cache_full  := MT2.empty
    )

  let xs_modulo_records t { Ty.lbs; _  } =
    List.rev
      (List.rev_map
         (fun (hs, ty) ->
            E.mk_term (Symbols.Op (Symbols.Access hs)) [t] ty) lbs)

  (* Set of lists of terms. *)
  module SLE =
    Set.Make(struct
      type t = E.t list

      let compare = Util.compare_lists ~cmp:E.compare
    end)

  (* Update the classes according to the equality modulo theory. *)
  let filter_classes mconf tbox cl =
    if mconf.Util.no_ematching then cl
    else
      let mtl =
        List.fold_left
          (fun acc xs ->
             let xs =
               List.rev_map (fun t -> X.term_repr tbox t ~init_term:false) xs
               |> List.rev
             in
             SLE.add xs acc
          ) SLE.empty cl
      in
      SLE.elements mtl

  let linear_arithmetic_matching (pat : E.t) (t : E.t) =
    let plus_of_minus d =
      [E.mk_term (Symbols.Op Symbols.Minus) [t; d] t.ty ; d]
    in
    let minus_of_plus d = [E.mk_plus t d t.ty; d] in
    if not (Options.get_arith_matching ()) ||
       t.ty != Ty.Tint && t.ty != Ty.Treal then []
    else
      match pat.f, pat.xs with
      | Symbols.Op Symbols.Plus, [p1; p2] ->
        if E.is_ground p2 then [plus_of_minus p2]
        else if E.is_ground p1 then [plus_of_minus p1] else []

      | Symbols.Op Symbols.Minus, [p1; p2] ->
        if E.is_ground p2 then [minus_of_plus p2]
        else if E.is_ground p1 then [minus_of_plus p1] else []
      | _ -> []

  (* Extend the substitution [sbt] by the binding [f -> t].
     The function raises an Echec exception if we cannot extend the
     substitution according the union-find UF(X). *)
  let add_msymb tbox f t ({ content = (sbt_t, sbt_ty); _ } as sbt)
      ~max_t_depth =
    try
      match Expr.TSubst.apply sbt_t f with
      | s when not @@ are_equal ~mode:`Full tbox t s -> raise Echec
      | _ -> sbt
    with Not_found -> begin
        let t =
          if (E.depth t) > max_t_depth || get_normalize_instances () then
            X.term_repr tbox t ~init_term:true
          else t
        in
        { sbt with content = (Expr.TSubst.assign f t sbt_t, sbt_ty) }
      end

  let rm x lst = List.filter (fun y -> E.compare x y <> 0) lst

  let rec permutations = function
    | [] -> []
    | x :: [] -> [[x]]
    | lst ->
      List.fold_left (fun acc x ->
          acc @ List.map (fun p -> x :: p) (permutations (rm x lst))
        ) [] lst

  let match_classes mconf tbox (pat : E.t) term =
    let cl =
      if mconf.Util.no_ematching then [term]
      else X.class_of tbox term
    in
    Debug.match_class_of term cl;
    let cl =
      List.fold_left
        (fun cls (term : E.t) ->
           if Symbols.compare pat.f term.f = 0 then
             if Sy.is_infix_operator pat.f then
               List.rev_append (permutations term.xs) cls
             else
               term.xs :: cls
           else
             begin
               match pat.f, term.ty with
               | Symbols.Op (Symbols.Record), Ty.Trecord record ->
                 (xs_modulo_records term record) :: cls
               | _ -> cls
             end
        ) [] cl
      |> filter_classes mconf tbox
    in
    if cl != [] then cl
    else linear_arithmetic_matching pat term

  (* Produce candidate substitutions to match the pattern [pat] with the
     term [term]. *)
  let rec match_term mconf env tbox sbt pat term =
    Options.exec_thread_yield ();
    Debug.match_term sbt term pat;
    let sbt =
      let (sbt_t, sbt_ty) = sbt.content in
      let sbt_ty =
        try
          Ty.matching sbt_ty pat.ty (E.type_info term)
        with Ty.TypeClash _ -> raise Echec
      in
      { sbt  with content = (sbt_t, sbt_ty) }
    in
    match pat.f with
    | Symbols.Var _ when Symbols.equal pat.f Symbols.underscore -> [sbt]
    | Symbols.Var _ ->
      let sbt =
        let age, from_goal =
          try
            let info = Expr.Map.find term env.known_terms in
            info.age, info.from_goal
          with Not_found -> 0, false
        in
        {
          sbt with
          age = max sbt.age age;
          from_goal = sbt.from_goal || from_goal
        }
      in
      [add_msymb tbox pat.f term sbt ~max_t_depth:env.max_t_depth]
    | _ ->
      try
        if E.is_ground pat && are_equal ~mode:`Light tbox pat term then [sbt]
        else
          let cl = match_classes mconf tbox pat term in
          List.fold_left
            (fun acc xs ->
               try match_list mconf env tbox sbt pat.xs xs @ acc
               with Echec -> acc
            ) [] cl
      with Ty.TypeClash _ -> raise Echec

  and match_list mconf env tbox (sbt : subst) pats terms =
    try
      Debug.match_list sbt pats terms;
      List.fold_left2
        (fun sbts pat term ->
           List.fold_left
             (fun acc2 sbt ->
                match_term mconf env tbox sbt pat term
                |> List.rev_append acc2
             ) [] sbts
        ) [sbt] pats terms
    with Invalid_argument _ -> raise Echec

  (* Collect all the extensions of the substitution [sbt] by
     bindings of the form [f -> term] where [term] is a known term whose the
     type matches the type [ty]. *)
  let match_var env tbox acc (pat : Expr.t)
      ({ content = (sbt_t, sbt_ty); _ } as sbt) =
    Expr.Map.fold
      (fun term (info : term_info) sbts ->
         try
           let sbt_ty = Ty.matching sbt_ty pat.ty (E.type_info term) in
           (* With triggers that are variables, always normalize
              substitutions. *)
           let term = X.term_repr tbox term ~init_term:true in
           let sbt_t = Expr.TSubst.assign pat.f term sbt_t in
           let sbt = { sbt with
                       content = (sbt_t, sbt_ty);
                       age = Int.max sbt.age info.age;
                       from_goal = sbt.from_goal || info.from_goal;
                       terms_orig = term :: sbt.terms_orig
                     }
           in
           sbt :: sbts
         with Ty.TypeClash _ -> sbts
      ) env.known_terms acc

  (* Trying to match the pattern [pat] with any known term by
     extending the annotated substitution [sbt]. *)
  let match_one_pat mconf env tbox pat acc sbt =
    Steps.incr (Steps.Matching);
    Debug.match_one_pat sbt pat;
    let pat = Expr.apply_subst sbt.content pat in
    let sbt_t, sbt_ty = sbt.content in
    match pat.f with
    | Symbols.Var _ -> match_var env tbox acc pat sbt
    | _ ->
      try
        let map_f = Symbols.Map.find pat.f env.fils in
        (* Try to match the arguments of the pattern [pat] with the argument of
           the term [t]. *)
        Expr.Set.fold
          (fun term acc ->
             Debug.match_one_pat_against sbt pat term;
             if E.depth term > 5 * env.max_t_depth then acc
             else
               try
                 let sbt =
                   let sbt_ty = Ty.matching sbt_ty pat.ty (E.type_info term) in
                   { sbt with content = (sbt_t, sbt_ty) }
                 in
                 match_list mconf env tbox sbt pat.xs term.xs
                 |> List.rev_append acc
               with Echec | Ty.TypeClash _ -> acc
          ) map_f acc
      with Not_found ->
        (* Aborting if there is no known term whose the top symbol is pat.f. *)
        acc

  (* Trying to match the pattern [pat] with any known term by applying
     some extensions of the substitutions [sbts].
     Return a list of substitutions that match the pattern [pat] with
     some known terms. *)
  let match_pat_modulo mconf env tbox sbts pat =
    Debug.match_pat_modulo pat sbts;
    List.fold_left (match_one_pat mconf env tbox pat) [] sbts

  let trig_weight s t =
    match E.term_view s, E.term_view t with
    | E.Not_a_term _, _ | _, E.Not_a_term _ -> assert false
    | E.Term { E.f = Symbols.Name _; _ },
      E.Term { E.f = Symbols.Op _; _ }   -> -1
    | E.Term { E.f = Symbols.Op _; _ },
      E.Term { E.f = Symbols.Name _; _ } -> 1
    | _ -> (E.depth t) - (E.depth s)

  (* Produce a list of candidate substitutions for the annoted trigger [tr].
     The trigger is ignored if its number of patterns exceed the value
     of the option [get_max_multi_triggers_size]. *)
  let matching mconf env tbox tr =
    let pats = List.stable_sort trig_weight tr.E.content in
    Debug.matching tr;
    if List.length pats > Options.get_max_multi_triggers_size () then []
    else
      (* This counter prevents to producing too much substitutions. *)
      let cpt = ref 1 in
      let tr_info = Expr.Trigger.Map.find tr env.known_triggers in
      try
        let id = {
          content = Expr.Subst.id;
          age = 0;
          lemma_orig = tr_info.lemma_orig;
          terms_orig = [];
          from_goal = false;
        }
        in
        let res =
          List.fold_left
            (fun acc pat ->
               let acc = match_pat_modulo mconf env tbox acc pat in
               let len = List.length acc in
               cpt := !cpt * len;
               if !cpt = 0 || !cpt > 1_000_000 then raise Exit;
               acc
            ) [id] pats
        in
        Debug.candidate_substitutions tr tr_info res;
        res
      with Exit ->
        if get_debug_matching() >= 1 && get_verbose() then begin
          Printer.print_dbg
            ~module_name:"Matching" ~function_name:"matching"
            "skip matching for %%a : cpt = %d"
            !cpt
        end;
        []

  let query mconf env tbox =
    reset_cache_refs ();
    try
      let res =
        Expr.Trigger.Map.fold
          (fun tr info acc -> (tr, info, matching mconf env tbox tr) :: acc)
          env.known_triggers []
      in
      reset_cache_refs ();
      res
    with e ->
      reset_cache_refs ();
      raise e

  let query env tbox =
    if Options.get_timers() then
      try
        Timers.exec_timer_start Timers.M_Match Timers.F_query;
        let res = query env tbox in
        Timers.exec_timer_pause Timers.M_Match Timers.F_query;
        res
      with e ->
        Timers.exec_timer_pause Timers.M_Match Timers.F_query;
        raise e
    else query env tbox

  let max_term_depth env mx = {env with max_t_depth = max env.max_t_depth mx}

  (* unused --
     let fully_uninterpreted_head s =
     match E.term_view s with
     | E.Not_a_term _ -> assert false
     | E.Term { E.f = Symbols.Op _; _ } -> false
     | _ -> true

     (* this function removes "big triggers"
        that are subsumed by smaller ones *)
     let filter_subsumed_triggers triggers =
     List.fold_left
      (fun acc tr ->
         match tr.E.content with
         | [t] ->
           let subterms = E.sub_terms E.Set.empty t in
           if List.exists (fun tr ->
               match tr.E.content with
               | [s] ->
                 not (E.equal s t) && E.Set.mem s subterms &&
                 fully_uninterpreted_head s
               | _ -> false
             )triggers
           then
             acc
           else
             tr :: acc
         | _ -> tr :: acc
      )[] triggers |> List.rev
  *)

  module HEI = Hashtbl.Make (
    struct
      open Util
      type t = E.t * Util.matching_env
      let hash (e, mc) =
        abs @@
        E.hash e *
        (mc.nb_triggers +
         (if mc.triggers_var then 10 else -10) +
         (if mc.greedy then 50 else - 50)
        )

      let equal (e1, mc1) (e2, mc2) =
        E.equal e1 e2 &&
        mc1.nb_triggers == mc2.nb_triggers &&
        mc1.triggers_var == mc2.triggers_var &&
        mc1.greedy == mc2.greedy

    end)

  module HE = Hashtbl.Make (E)

  let normal_triggers =
    let trs_tbl = HEI.create 101 in
    fun q mconf ->
      match q.E.user_trs with
      | _::_ as l -> l
      | [] ->
        try HEI.find trs_tbl (q.E.main, mconf)
        with Not_found ->
          let trs = E.Trigger.make q.E.main q.E.binders q.E.kind mconf in
          HEI.add trs_tbl (q.E.main, mconf) trs;
          trs

  let backward_triggers =
    let trs_tbl = HE.create 101 in
    fun q ->
      try HE.find trs_tbl q.E.main
      with Not_found ->
        let trs = E.resolution_triggers ~is_back:true q in
        HE.add trs_tbl q.E.main trs;
        trs

  let forward_triggers =
    let trs_tbl = HE.create 101 in
    fun q ->
      try HE.find trs_tbl q.E.main
      with Not_found ->
        let trs = E.resolution_triggers ~is_back:false q in
        HE.add trs_tbl q.E.main trs;
        trs

  let add_triggers mconf =
    Expr.Map.fold
      (fun lemma (age, increm_guard, dep) env ->
         match E.form_view lemma with
         | E.Lemma ({ main; name; _ } as q) ->
           let triggers, kind =
             match mconf.Util.inst_mode with
             | Util.Normal   -> normal_triggers q mconf, "Normal"
             | Util.Backward -> backward_triggers q, "Backward"
             | Util.Forward  -> forward_triggers q, "Forward"
           in
           if get_debug_triggers () then
             Printer.print_dbg
               ~module_name:"Matching" ~function_name:"add_triggers"
               "@[<v 2>%s triggers of %s are:@ %a@]"
               kind name E.print_triggers triggers;
           List.fold_left
             (fun env trigger ->
                let info = {
                  age;
                  lemma_orig = lemma;
                  formula_orig = main;
                  dep;
                  increm_guard;
                }
                in
                let known_triggers =
                  Expr.Trigger.Map.add trigger info env.known_triggers
                in
                { env with known_triggers }
             ) env triggers

         | E.Unit _ | E.Clause _ | E.Literal _ | E.Skolem _
         | E.Let _ | E.Iff _ | E.Xor _ | E.Not_a_form -> assert false
      )

end
