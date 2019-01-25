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
module ME = Expr.Map
module SE = Expr.Set
module Ex = Explanation

module type S = sig
  type t
  type tbox
  type instances = (Expr.gformula * Ex.t) list

  val empty : t
  val add_terms : t -> SE.t -> Expr.gformula -> t
  val add_lemma : t -> Expr.gformula -> Ex.t -> t
  val add_predicate : t -> Expr.gformula -> Ex.t -> t

  val m_lemmas :
    Util.matching_env ->
    t ->
    tbox ->
    (E.t -> E.t -> bool) ->
    int ->
    instances * instances (* goal_directed, others *)

  val m_predicates :
    Util.matching_env ->
    t ->
    tbox ->
    (E.t -> E.t -> bool) ->
    int ->
    instances * instances (* goal_directed, others *)

  val register_max_term_depth : t -> int -> t

  val matching_terms_info :
    t -> Matching_types.info Expr.Map.t * Expr.t list Expr.Map.t Symbols.Map.t

end

module Make(X : Theory.S) : S with type tbox = X.t = struct

  module EM = Matching.Make(Ccx.Main)

  type tbox = X.t
  type instances = (Expr.gformula * Ex.t) list

  type t = {
    lemmas : (int * Ex.t) ME.t;
    predicates : (int * Ex.t) ME.t;
    matching : EM.t;
  }

  let empty = {
    lemmas = ME.empty ;
    matching = EM.empty;
    predicates = ME.empty;
  }

  module Debug = struct

    let new_facts_of_axiom ax insts_ok =
      if debug_matching () >= 1 && insts_ok != ME.empty then
        let name = match Expr.form_view ax with
          | E.Lemma { E.name = s; _ } -> s
          | E.Unit _ | E.Clause _ | E.Literal _ | E.Skolem _
          | E.Let _ | E.Iff _ | E.Xor _ -> "!(no-name)"
          | E.Not_a_form -> assert false
        in
        fprintf fmt "[Instances.split_and_filter_insts] ";
        fprintf fmt "%3d different new instances generated for %s@."
          (ME.cardinal insts_ok) name


    let new_mround ilvl kind =
      if debug_matching () >= 1 then
        fprintf fmt "@.# [matching] new %s matching round: ilevel = %d...@."
          kind ilvl

  end

  let add_terms env s gf =
    let infos = {
      Matching_types.term_age = gf.Expr.age ;
      term_from_goal    = gf.Expr.gf ;
      term_from_formula = gf.Expr.lem ;
      term_from_terms   = gf.Expr.from_terms
    }
    in
    { env with
      matching = SE.fold (EM.add_term infos) s env.matching }

  let add_predicate env gf ex =
    let { Expr.ff = f; age = age; _ } = gf in
    { env with
      predicates = ME.add f (age, ex) env.predicates;
      (* this is not done in SAT*)
      matching = EM.max_term_depth env.matching (E.depth f)
    }

  let register_max_term_depth env mx =
    {env with matching = EM.max_term_depth env.matching mx}

  let record_this_instance f accepted lorig =
    match Expr.form_view lorig with
    | E.Lemma { E.name; loc; _ } ->
      Profiling.new_instance_of name f loc accepted
    | E.Unit _ | E.Clause _ | E.Literal _ | E.Skolem _
    | E.Let _ | E.Iff _ | E.Xor _ | E.Not_a_form -> assert false

  let profile_produced_terms env lorig nf s trs =
    let st0 =
      List.fold_left (fun st t -> E.sub_terms st (E.apply_subst s t))
        SE.empty trs
    in
    let name, loc, _ = match Expr.form_view lorig with
      | E.Lemma { E.name; main; loc; _ } -> name, loc, main
      | E.Unit _ | E.Clause _ | E.Literal _ | E.Skolem _
      | E.Let _ | E.Iff _ | E.Xor _ | E.Not_a_form -> assert false
    in
    let st1 = E.max_ground_terms_rec_of_form nf in
    let diff = Expr.Set.diff st1 st0 in
    let info, _ = EM.terms_info env.matching in
    let _new = Expr.Set.filter (fun t -> not (ME.mem t info)) diff in
    Profiling.register_produced_terms name loc st0 st1 diff _new

  let inst_is_seen_during_this_round orig f insts =
    try
      let mp_orig_ok, mp_orig_ko = ME.find orig insts in
      ME.mem f mp_orig_ok || SE.mem f mp_orig_ko
    with Not_found -> false

  let add_accepted_to_acc orig f item insts =
    let mp_orig_ok, mp_orig_ko =
      try ME.find orig insts with Not_found -> ME.empty, SE.empty
    in
    assert (not (ME.mem f mp_orig_ok));
    assert (not (SE.mem f mp_orig_ko));
    ME.add orig (ME.add f item mp_orig_ok, mp_orig_ko) insts

  let add_rejected_to_acc orig f insts =
    let mp_orig_ok, mp_orig_ko =
      try ME.find orig insts with Not_found -> ME.empty, SE.empty
    in
    assert (not (ME.mem f mp_orig_ok));
    assert (not (SE.mem f mp_orig_ko));
    ME.add orig (mp_orig_ok, SE.add f mp_orig_ko) insts


  let new_facts _env tbox selector substs =
    List.fold_left
      (fun acc ({Matching_types.trigger_formula=f;
                 trigger_age=age; trigger_dep=dep; trigger_orig=orig;
                 trigger = tr},
                subst_list) ->
        let cpt = ref 0 in
        let kept = ref 0 in
        List.fold_left
          (fun acc
            {Matching_types.sbs = sbs;
             sty = sty;
             gen = g;
             goal = b;
             s_term_orig = torig;
             s_lem_orig = lorig} ->
            incr cpt;
            let s = sbs, sty in
            match tr.E.guard with
            | Some a when X.query (Expr.apply_subst s a) tbox==None -> acc
            | _ ->
              let nf = E.apply_subst s f in
              if inst_is_seen_during_this_round orig nf acc then acc
              else
                let accepted = selector nf orig in
                if not accepted then add_rejected_to_acc orig nf acc
                else
                  let p =
                    { Expr.ff = nf;
                      origin_name = E.name_of_lemma lorig;
                      gdist = -1;
                      hdist = -1;
                      trigger_depth = tr.Expr.t_depth;
                      nb_reductions = 0;
                      age = 1+(max g age);
                      mf = true;
                      gf = b;
                      lem = Some lorig;
                      from_terms = torig;
                      theory_elim = true
                    }
                  in
                  let dep =
                    if not (Options.unsat_core() || Options.profiling()) then
                      dep
                    else
                      (* Dep lorig used to track conflicted instances
                         in profiling mode *)
                      Ex.union dep (Ex.singleton (Ex.Dep lorig))
                  in
                  incr kept;
                  add_accepted_to_acc orig nf (p, dep, s, tr.E.content) acc
          ) acc subst_list
      ) ME.empty substs


  let split_and_filter_insts env insts =
    ME.fold
      (fun orig (mp_orig_ok, mp_orig_ko) acc ->
         Debug.new_facts_of_axiom orig mp_orig_ok;
         let acc =
           ME.fold
             (fun _ (p, dep, _, _) (gd, ngd) ->
                if p.Expr.gf then (p, dep) :: gd, ngd else gd, (p, dep) :: ngd
             )mp_orig_ok acc
         in
         if Options.profiling() then
           begin (* update profiler data *)
             SE.iter (fun f -> record_this_instance f false orig) mp_orig_ko;
             ME.iter (fun f (_, _, name, tr_ctt) ->
                 profile_produced_terms env orig f name tr_ctt;
                 record_this_instance f true orig
               ) mp_orig_ok;
           end;
         acc
      )insts ([], [])


  let sort_facts =
    let rec size f = match Expr.form_view f with
      | E.Unit(f1,f2) -> max (size f1) (size f2)
      | E.Lemma _ | E.Clause _ | E.Literal _ | E.Skolem _
      | E.Let _ | E.Iff _ | E.Xor _ -> E.size f
      | E.Not_a_form -> assert false
    in
    fun lf ->
      List.fast_sort
        (fun (p1,_) (p2,_) ->
           let c = size p1.Expr.ff - size p2.Expr.ff in
           if c <> 0 then c
           else E.compare p2.Expr.ff p1.Expr.ff
        ) lf

  let new_facts env tbox selector substs =
    if Options.timers() then
      try
        Timers.exec_timer_start Timers.M_Match Timers.F_new_facts;
        let res = new_facts env tbox selector substs in
        Timers.exec_timer_pause Timers.M_Match Timers.F_new_facts;
        res
      with e ->
        Timers.exec_timer_pause Timers.M_Match Timers.F_new_facts;
        raise e
    else new_facts env tbox selector substs

  let mround env axs tbox selector ilvl kind mconf =
    Debug.new_mround ilvl kind;
    Options.tool_req 2 "TR-Sat-Mround";
    let env =
      {env with matching = EM.add_triggers mconf env.matching axs} in
    let ccx_tbox =
      if mconf.Util.use_cs || mconf.Util.greedy then X.get_case_split_env tbox
      else X.get_real_env tbox
    in
    let substs = EM.query mconf env.matching ccx_tbox in
    let insts = new_facts env tbox selector substs in
    let gd, ngd = split_and_filter_insts env insts in
    sort_facts gd, sort_facts ngd

  let m_lemmas env tbox selector ilvl mconf =
    mround env env.lemmas tbox selector ilvl "axioms" mconf

  let m_predicates env tbox selector ilvl mconf =
    mround env env.predicates tbox selector ilvl "predicates" mconf

  let add_lemma env gf dep =
    let { Expr.ff = orig; age = age; _ } = gf in
    let age, dep =
      try
        let age' , dep' = ME.find orig env.lemmas in
        min age age' , Ex.union dep dep'
      with Not_found -> age, dep
    in
    { env with lemmas = ME.add orig (age,dep) env.lemmas }

  (*** add wrappers to profile exported functions ***)

  let add_terms env s gf =
    if Options.timers() then
      try
        Timers.exec_timer_start Timers.M_Match Timers.F_add_terms;
        let res = add_terms env s gf in
        Timers.exec_timer_pause Timers.M_Match Timers.F_add_terms;
        res
      with e ->
        Timers.exec_timer_pause Timers.M_Match Timers.F_add_terms;
        raise e
    else add_terms env s gf

  let add_lemma env gf dep =
    if Options.timers() then
      try
        Timers.exec_timer_start Timers.M_Match Timers.F_add_lemma;
        let res = add_lemma env gf dep in
        Timers.exec_timer_pause Timers.M_Match Timers.F_add_lemma;
        res
      with e ->
        Timers.exec_timer_pause Timers.M_Match Timers.F_add_lemma;
        raise e
    else add_lemma env gf dep

  let add_predicate env gf =
    if Options.timers() then
      try
        Timers.exec_timer_start Timers.M_Match Timers.F_add_predicate;
        let res = add_predicate env gf in
        Timers.exec_timer_pause Timers.M_Match Timers.F_add_predicate;
        res
      with e ->
        Timers.exec_timer_pause Timers.M_Match Timers.F_add_predicate;
        raise e
    else add_predicate env gf

  let m_lemmas mconf env tbox selector ilvl =
    if Options.timers() then
      try
        Timers.exec_timer_start Timers.M_Match Timers.F_m_lemmas;
        let res = m_lemmas env tbox selector ilvl mconf in
        Timers.exec_timer_pause Timers.M_Match Timers.F_m_lemmas;
        res
      with e ->
        Timers.exec_timer_pause Timers.M_Match Timers.F_m_lemmas;
        raise e
    else m_lemmas env tbox selector ilvl mconf

  let m_predicates mconf env tbox selector ilvl =
    if Options.timers() then
      try
        Timers.exec_timer_start Timers.M_Match Timers.F_m_predicates;
        let res = m_predicates env tbox selector ilvl mconf in
        Timers.exec_timer_pause Timers.M_Match Timers.F_m_predicates;
        res
      with e ->
        Timers.exec_timer_pause Timers.M_Match Timers.F_m_predicates;
        raise e
    else m_predicates env tbox selector ilvl mconf

  let matching_terms_info env = EM.terms_info env.matching

end
