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
  val add_predicate :
    t ->
    guard:Expr.t ->
    name:string ->
    Expr.gformula ->
    Ex.t ->
    t

  val ground_pred_defn:
    Expr.t -> t -> (Expr.t * Expr.t * Explanation.t) option

  val pop : t -> guard:Expr.t -> t

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

  val reinit_em_cache : unit -> unit

end

module Make(X : Theory.S) : S with type tbox = X.t = struct

  module EM = Matching.Make(struct

      include Ccx.Main

      (* This function from Ccx.Main is wrapped to ensure Fresh explanations
         will not leak through Ccx during matching, in which case assertions
         in various places will be raised. *)
      let term_repr t e ~init_term =
        try Ccx.Main.term_repr t ~init_term e
        with Ex.Inconsistent (d, _) as exn ->
          if Ex.exists_fresh d then e else raise exn

    end)

  type tbox = X.t
  type instances = (Expr.gformula * Ex.t) list

  type guard = E.t

  type t = {
    guards : (E.t * bool) list ME.t;
    (* from guards to list of guarded predicates.
       bool = true <-> pred is ground *)
    lemmas : (guard * int * Ex.t) ME.t;
    predicates : (guard * int * Ex.t) ME.t;
    ground_preds : (guard * E.t * Explanation.t) ME.t; (* key <-> f *)
    matching : EM.t;
  }

  let empty = {
    guards = ME.empty;
    lemmas = ME.empty ;
    matching = EM.empty;
    predicates = ME.empty;
    ground_preds = ME.empty
  }

  module Debug = struct
    open Printer

    let new_facts_of_axiom ax insts_ok =
      if get_debug_matching () >= 1 && insts_ok != ME.empty then
        let name = match Expr.form_view ax with
          | E.Lemma { E.name = s; _ } -> s
          | E.Unit _ | E.Clause _ | E.Literal _ | E.Skolem _
          | E.Let _ | E.Iff _ | E.Xor _ -> "!(no-name)"
        in
        print_dbg
          ~module_name:"Instances" ~function_name:"new_facts_of_axiom"
          "[Instances.split_and_filter_insts]@ \
           %3d different new instances generated for %s"
          (ME.cardinal insts_ok) name

    let new_mround ilvl kind =
      if get_debug_matching () >= 1 then
        print_dbg
          ~module_name:"Instance" ~function_name:"new_mround"
          "[matching] new %s matching round: ilevel = %d..."
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

  let add_ground_pred env ~guard p np defn ex =
    let gp = ME.add p (guard, defn, ex) env.ground_preds in
    let gp = ME.add np (guard, E.neg defn, ex) gp in
    let guarded = try ME.find guard env.guards with Not_found -> [] in
    let guarded = (p, true) :: (np, true) :: guarded in
    { env with ground_preds = gp;
               guards = ME.add guard guarded env.guards
    }


  let add_predicate env ~guard ~name gf ex =
    let { Expr.ff = f; age = age; _ } = gf in
    let env = { env with
                matching = EM.max_term_depth env.matching (E.depth f) } in
    match E.form_view f with
    | E.Iff(f1, f2) ->
      let p = E.mk_term (Symbols.name @@ Uid.of_string name) [] Ty.Tbool in
      let np = E.neg p in
      let defn =
        if E.equal f1 p then f2
        else if E.equal f2 p then f1
        else assert false
      in
      add_ground_pred env ~guard p np defn ex

    | E.Literal _ ->
      let p = E.mk_term (Symbols.name @@ Uid.of_string name) [] Ty.Tbool in
      let np = E.neg p in
      let defn =
        if E.equal p f then E.vrai
        else if E.equal np f then E.faux
        else assert false
      in
      add_ground_pred env ~guard p np defn ex

    | E.Lemma _ ->
      let guarded = try ME.find guard env.guards with Not_found -> [] in
      { env with
        predicates = ME.add f (guard, age, ex) env.predicates;
        guards = ME.add guard ((f, false) :: guarded) env.guards
      }
    | E.Unit _ | E.Clause _ | E.Xor _
    | E.Skolem _ | E.Let _ ->
      assert false

  let pop env ~guard =
    try
      let guarded = ME.find guard env.guards in
      let ground, non_ground =
        List.fold_left
          (fun (ground, non_ground) (f, is_ground) ->
             if is_ground then ME.remove f ground, non_ground
             else ground, ME.remove f non_ground
          )(env.ground_preds, env.predicates) guarded
      in
      { env with guards = ME.remove guard env.guards;
                 predicates = non_ground;
                 ground_preds = ground }
    with Not_found ->
      env

  let ground_pred_defn (p : E.t) env =
    try Some (ME.find p env.ground_preds)
    with Not_found -> None

  let register_max_term_depth env mx =
    {env with matching = EM.max_term_depth env.matching mx}

  let record_this_instance f accepted lorig =
    match Expr.form_view lorig with
    | E.Lemma { E.name; loc; _ } ->
      Profiling.new_instance_of name f loc accepted
    | E.Unit _ | E.Clause _ | E.Literal _ | E.Skolem _
    | E.Let _ | E.Iff _ | E.Xor _ -> assert false

  let profile_produced_terms env lorig nf s trs =
    let st0 =
      List.fold_left (fun st t -> E.sub_terms st (E.apply_subst s t))
        SE.empty trs
    in
    let name, loc, _ = match Expr.form_view lorig with
      | E.Lemma { E.name; main; loc; _ } -> name, loc, main
      | E.Unit _ | E.Clause _ | E.Literal _ | E.Skolem _
      | E.Let _ | E.Iff _ | E.Xor _ -> assert false
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


  let new_facts _env _tbox selector substs =
    List.fold_left
      (fun acc ({Matching_types.trigger_formula=f;
                 trigger_age=age; trigger_dep=dep; trigger_orig=orig;
                 trigger = tr; trigger_increm_guard},
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
            let nf = E.apply_subst s f in
            (* add the incrementaly guard to nf, if any *)
            let nf = E.mk_imp trigger_increm_guard nf in
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
                  if not (Options.get_unsat_core() ||
                          Options.get_profiling()) then
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
         if Options.get_profiling() then
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
    in
    fun lf ->
      List.fast_sort
        (fun (p1,_) (p2,_) ->
           let c = size p1.Expr.ff - size p2.Expr.ff in
           if c <> 0 then c
           else E.compare p2.Expr.ff p1.Expr.ff
        ) lf

  let new_facts env tbox selector substs =
    Timers.with_timer Timers.M_Match Timers.F_new_facts @@ fun () ->
    new_facts env tbox selector substs

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
    let guard = E.vrai in
    (* lemmas are already guarded outside instances.ml *)
    let { Expr.ff = orig; age = age; _ } = gf in
    let age, dep =
      try
        let _, age' , dep' = ME.find orig env.lemmas in
        min age age' , Ex.union dep dep'
      with Not_found -> age, dep
    in
    { env with lemmas = ME.add orig (guard, age,dep) env.lemmas }

  let matching_terms_info env = EM.terms_info env.matching

  let reinit_em_cache () = EM.reinit_caches ()

  (*** add wrappers to profile exported functions ***)

  let add_terms env s gf =
    Timers.with_timer Timers.M_Match Timers.F_add_terms @@ fun () ->
    add_terms env s gf

  let add_lemma env gf dep =
    Timers.with_timer Timers.M_Match Timers.F_add_lemma @@ fun () ->
    add_lemma env gf dep

  let add_predicate env ~guard ~name gf =
    Timers.with_timer Timers.M_Match Timers.F_add_predicate @@ fun () ->
    add_predicate env ~guard ~name gf

  let m_lemmas mconf env tbox selector ilvl =
    Timers.with_timer Timers.M_Match Timers.F_m_lemmas @@ fun () ->
    m_lemmas env tbox selector ilvl mconf

  let m_predicates mconf env tbox selector ilvl =
    Timers.with_timer Timers.M_Match Timers.F_m_predicates @@ fun () ->
    m_predicates env tbox selector ilvl mconf

end
