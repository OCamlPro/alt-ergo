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

module T = Term
module F = Formula
module MF = F.Map
module SF = F.Set
module Ex = Explanation
module MT = T.Map


module type S = sig
  type t
  type tbox
  type instances = (F.gformula * Ex.t) list

  val empty : t
  val add_terms : t -> T.Set.t -> F.gformula -> t
  val add_lemma : t -> F.gformula -> Ex.t -> t * instances
  val add_predicate : t -> F.gformula -> t

  val m_lemmas :
    backward:Util.inst_kind ->
    t ->
    tbox ->
    (F.t -> F.t -> bool) ->
    int ->
    instances * instances (* goal_directed, others *)

  val m_predicates :
    backward:Util.inst_kind ->
    t ->
    tbox ->
    (F.t -> F.t -> bool) ->
    int ->
    instances * instances (* goal_directed, others *)

  (* returns used axioms/predicates * unused axioms/predicates *)
  val retrieve_used_context : t -> Ex.t -> Formula.t list * Formula.t list

  val register_max_term_depth : t -> int -> t

  val matching_terms_info :
    t -> Matching_types.info Term.Map.t * Term.t list Term.Map.t Term.Subst.t

end

module Make(X : Theory.S) : S with type tbox = X.t = struct

  module EM = Matching.Make(
    struct
      include X
      let add_term env t = X.add_term env t ~add_in_cs:false
    end)

  type tbox = X.t
  type instances = (F.gformula * Ex.t) list

  type t = {
    lemmas : (int * Ex.t) MF.t;
    predicates : (int * Ex.t) MF.t;
    matching : EM.t;
  }

  let empty = {
    lemmas = MF.empty ;
    matching = EM.empty;
    predicates = MF.empty;
  }

  module Debug = struct

    let new_facts_of_axiom ax insts_ok =
      if debug_matching () >= 1 && insts_ok != MF.empty then
        let name = match F.view ax with
            F.Lemma {F.name=s} -> s | _ -> "!(no-name)"
        in
        fprintf fmt "[Instances.split_and_filter_insts] ";
        fprintf fmt "%3d different new instances generated for %s@."
          (MF.cardinal insts_ok) name


    let new_mround ilvl kind =
      if debug_matching () >= 1 then
        fprintf fmt "@.# [matching] new %s matching round: ilevel = %d...@."
          kind ilvl

  end

  let add_terms env s gf =
    let infos = {
      Matching_types.term_age = gf.F.age ;
      term_from_goal    = gf.F.gf ;
      term_from_formula = gf.F.lem ;
      term_from_terms   = gf.F.from_terms
    }
    in
    { env with
      matching = T.Set.fold (EM.add_term infos) s env.matching }

  let add_predicate env gf =
    let {F.f=f;age=age} = gf in
    if EM.unused_context f then env
    else
      { env with
        predicates = MF.add f (age,Ex.empty) env.predicates;
        (* this is not done in SAT*)
        matching = EM.max_term_depth env.matching (F.max_term_depth f)
      }

  let register_max_term_depth env mx =
    {env with matching = EM.max_term_depth env.matching mx}

  let record_this_instance f accepted lorig =
    match F.view lorig with
    | F.Lemma {F.name;loc} -> Profiling.new_instance_of name f loc accepted
    | _ -> assert false

  let profile_produced_terms env lorig nf s trs =
    let st0 =
      List.fold_left (fun st t -> T.subterms st (T.apply_subst s t))
        T.Set.empty trs
    in
    let name, loc, f = match F.view lorig with
      | F.Lemma {F.name;main;loc} -> name, loc, main
      | _ -> assert false
    in
    let st1 = F.ground_terms_rec nf in
    let diff = Term.Set.diff st1 st0 in
    let info, _ = EM.terms_info env.matching in
    let _new = Term.Set.filter (fun t -> not (MT.mem t info)) diff in
    Profiling.register_produced_terms name loc st0 st1 diff _new

  let inst_is_seen_during_this_round orig f insts =
    try
      let mp_orig_ok, mp_orig_ko = MF.find orig insts in
      MF.mem f mp_orig_ok || SF.mem f mp_orig_ko
    with Not_found -> false

  let add_accepted_to_acc orig f item insts =
    let mp_orig_ok, mp_orig_ko =
      try MF.find orig insts with Not_found -> MF.empty, SF.empty
    in
    assert (not (MF.mem f mp_orig_ok));
    assert (not (SF.mem f mp_orig_ko));
    MF.add orig (MF.add f item mp_orig_ok, mp_orig_ko) insts

  let add_rejected_to_acc orig f insts =
    let mp_orig_ok, mp_orig_ko =
      try MF.find orig insts with Not_found -> MF.empty, SF.empty
    in
    assert (not (MF.mem f mp_orig_ok));
    assert (not (SF.mem f mp_orig_ko));
    MF.add orig (mp_orig_ok, SF.add f mp_orig_ko) insts


  let new_facts env tbox selector substs =
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
	      match tr.F.guard with
	      | Some a when X.query (Literal.LT.apply_subst s a) tbox==No -> acc
	      | _ ->
		let nf = F.apply_subst s f in
                if inst_is_seen_during_this_round orig nf acc then acc
                else
                  let accepted = selector nf orig in
                  if not accepted then add_rejected_to_acc orig nf acc
                  else
		    let p =
		      { F.f = nf;
                        origin_name = F.name_of_lemma lorig;
                        gdist = -1;
                        hdist = -1;
                        trigger_depth = tr.F.depth;
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
                      if not (Options.proof() || Options.profiling()) then dep
                      else
                        (* Dep lorig used to track conflicted instances
                           in profiling mode *)
                        Ex.union dep (Ex.singleton (Ex.Dep lorig))
                    in
                    incr kept;
                    add_accepted_to_acc orig nf (p, dep, s, tr.F.content) acc
	  ) acc subst_list
      ) MF.empty substs


  let split_and_filter_insts env insts =
    MF.fold
      (fun orig (mp_orig_ok, mp_orig_ko) acc ->
        Debug.new_facts_of_axiom orig mp_orig_ok;
        let acc =
          MF.fold
            (fun f (p, dep, _, _) (gd, ngd) ->
              if p.F.gf then (p, dep) :: gd, ngd else gd, (p, dep) :: ngd
            )mp_orig_ok acc
        in
        if Options.profiling() then
          begin (* update profiler data *)
            SF.iter (fun f -> record_this_instance f false orig) mp_orig_ko;
            MF.iter (fun f (_, _, name, tr_ctt) ->
              profile_produced_terms env orig f name tr_ctt;
              record_this_instance f true orig
            ) mp_orig_ok;
          end;
        acc
      )insts ([], [])


  let sort_facts =
    let rec size f = match F.view f with
      | F.Unit(f1,f2) -> max (size f1) (size f2)
      | _             -> F.size f
    in
    fun lf ->
      List.fast_sort
        (fun (p1,_) (p2,_) ->
          let c = size p1.F.f - size p2.F.f in
          if c <> 0 then c
          else F.compare p2.F.f p1.F.f
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

  let mround env axs tbox selector ilvl kind backward =
    Debug.new_mround ilvl kind;
    Options.tool_req 2 "TR-Sat-Mround";
    let env =
      {env with matching = EM.add_triggers ~backward env.matching axs} in
    let substs = EM.query env.matching tbox in
    let insts = new_facts env tbox selector substs in
    let gd, ngd = split_and_filter_insts env insts in
    sort_facts gd, sort_facts ngd

  let m_lemmas env tbox selector ilvl backward =
    mround env env.lemmas tbox selector ilvl "axioms" backward

  let m_predicates env tbox selector ilvl backward =
    mround env env.predicates tbox selector ilvl "predicates" backward

  module MI = Map.Make (struct type t = int let compare = compare end)

  let retrieve_used_context env dep =
    let deps = Ex.formulas_of dep in
    let used, unlems, unpreds =
      SF.fold
        (fun f ((used, lems, preds) as acc) ->
          if MF.mem f lems then f :: used, MF.remove f lems, preds
          else if MF.mem f preds then f :: used, lems, MF.remove f preds
          else
            match F.view f with
            | F.Lemma _ ->
              (* An axiom that does not appear in lems because of inconsist. *)
              f :: used, lems, preds
            | _ -> acc
        ) deps ([], env.lemmas, env.predicates)
    in
    let unused = MF.fold (fun f _ acc -> f::acc) unlems [] in
    let unused = MF.fold (fun f _ acc -> f::acc) unpreds unused in
    used, unused


  let add_lemma env gf dep =
    let {F.f=orig;age=age;gf=b} = gf in
    if (*not (Ex.is_empty dep) ||*) EM.unused_context orig then env, []
    else
      let age, dep =
        try
          let age' , dep' = MF.find orig env.lemmas in
          min age age' , Ex.union dep dep'
        with Not_found -> age, dep
      in
      let env = { env with lemmas = MF.add orig (age,dep) env.lemmas } in
      match F.view orig with
      | F.Lemma {F.simple_inst = Some sbs; main; name} ->
        let nf = F.apply_subst sbs main in
	let p =
	  { F.f = nf;
            origin_name = name;
            gdist = -1;
            hdist = -1;
            trigger_depth = max_int;
            nb_reductions = 0;
	    age = age+1;
	    mf = true;
	    gf = b;
	    lem = Some orig;
	    from_terms = [];
	    theory_elim = true;
	  }
        in
        let dep =
          if not (Options.proof() || Options.profiling()) then dep
          else
                (* Dep lorig used to track conflicted instances
                   in profiling mode *)
            Ex.union dep (Ex.singleton (Ex.Dep orig))
        in
        let insts = add_accepted_to_acc orig nf (p, dep, sbs, []) MF.empty in
        let gd, ngd = split_and_filter_insts env insts in
        env, List.rev_append gd ngd

      | _ -> env, []


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

  let m_lemmas ~backward env tbox selector ilvl =
    if Options.timers() then
      try
	Timers.exec_timer_start Timers.M_Match Timers.F_m_lemmas;
	let res = m_lemmas env tbox selector ilvl backward in
	Timers.exec_timer_pause Timers.M_Match Timers.F_m_lemmas;
	res
      with e ->
	Timers.exec_timer_pause Timers.M_Match Timers.F_m_lemmas;
	raise e
    else m_lemmas env tbox selector ilvl backward

  let m_predicates ~backward env tbox selector ilvl =
    if Options.timers() then
      try
	Timers.exec_timer_start Timers.M_Match Timers.F_m_predicates;
	let res = m_predicates env tbox selector ilvl backward in
	Timers.exec_timer_pause Timers.M_Match Timers.F_m_predicates;
	res
      with e ->
	Timers.exec_timer_pause Timers.M_Match Timers.F_m_predicates;
	raise e
    else m_predicates env tbox selector ilvl backward

  let matching_terms_info env = EM.terms_info env.matching

end
