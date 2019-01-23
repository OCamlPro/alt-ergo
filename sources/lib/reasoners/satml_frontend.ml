(******************************************************************************)
(*                                                                            *)
(*     Alt-Ergo: The SMT Solver For Software Verification                     *)
(*     Copyright (C) 2013-2018 --- OCamlPro SAS                               *)
(*                                                                            *)
(*     This file is distributed under the terms of the license indicated      *)
(*     in the file 'License.OCamlPro'. If 'License.OCamlPro' is not           *)
(*     present, please contact us to clarify licensing.                       *)
(*                                                                            *)
(******************************************************************************)

module Make (Th : Theory.S) : Sat_solver_sig.S = struct

  open Options
  open Format

  module SAT = Satml.Make(Th)
  module Inst = Instances.Make(Th)
  module Ex = Explanation
  module E = Expr
  module ME = E.Map
  module SE = E.Set
  module Atom = Satml_types.Atom
  module FF = Satml_types.Flat_Formula

  let reset_refs () = SAT.reset_steps ()
  let get_steps () = SAT.get_steps ()

  type t = {
    satml : SAT.t;
    ff_hcons_env : FF.hcons_env;
    nb_mrounds : int;
    last_forced_normal : int;
    last_forced_greedy : int;
    gamma : (int * FF.t option) ME.t;
    conj : (int * SE.t) FF.Map.t;
    abstr_of_axs : (FF.t * Atom.atom) ME.t;
    axs_of_abstr : (E.t * Atom.atom) ME.t;
    proxies : (Atom.atom * Atom.atom list * bool) Util.MI.t;
    inst : Inst.t;
    ground_preds : (E.gformula * Ex.t) ME.t; (* key <-> f *)
    skolems : E.gformula ME.t; (* key <-> f *)
    add_inst: E.t -> bool;
  }

  let empty () =
    { gamma = ME.empty;
      satml = SAT.empty ();
      ff_hcons_env = FF.empty_hcons_env ();
      nb_mrounds = 0;
      last_forced_normal = 0;
      last_forced_greedy = 0;
      conj = FF.Map.empty;
      abstr_of_axs = ME.empty;
      axs_of_abstr = ME.empty;
      proxies = Util.MI.empty;
      inst = Inst.empty;
      ground_preds = ME.empty;
      skolems = ME.empty;
      add_inst = fun _ -> true;
    }

  let empty_with_inst add_inst =
    { (empty ()) with add_inst = add_inst }

  exception Sat of t
  exception Unsat of Explanation.t
  exception I_dont_know of t

  exception IUnsat of t * Explanation.t

  let mk_gf f =
    { E.ff = f;
      trigger_depth = max_int;
      nb_reductions = 0;
      origin_name = "<none>";
      age = 0;
      lem = None;
      mf = false;
      gf = false;
      gdist = -1;
      hdist = -1;
      from_terms = [];
      theory_elim = true;
    }


  (*BISECT-IGNORE-BEGIN*)
  module Debug = struct

    let pred_def f =
      if debug_sat () then
        eprintf "[sat] I assume a predicate: %a@.@." E.print f

    let unsat gf =
      if debug_sat () then
        printf "[sat] unsat of %a ?@." E.print gf.E.ff

    let assume gf =
      let { E.ff = f; lem; from_terms = terms; _ } = gf in
      if debug_sat () then begin
        match E.form_view f with
        | E.Not_a_form -> assert false

        | E.Unit _ -> ()

        | E.Clause _ ->
          fprintf fmt "[sat] I assume a clause %a@." E.print f

        | E.Lemma _ ->
          fprintf fmt "[sat] I assume a [%d-atom] lemma: %a@."
            (E.size f) E.print f

        | E.Literal a ->
          E.print_list str_formatter terms;
          let s = flush_str_formatter () in
          let n = match lem with
            | None -> ""
            | Some ff ->
              (match E.form_view ff with
               | E.Lemma xx -> xx.E.name
               | E.Unit _ | E.Clause _ | E.Literal _ | E.Skolem _
               | E.Let _ | E.Iff _ | E.Xor _ -> ""
               | E.Not_a_form -> assert false)
          in
          fprintf fmt "\n[sat]I assume a literal (%s : %s) %a@]@."
            n s E.print a;
          fprintf fmt "================================================@.@."

        | E.Skolem _ ->
          fprintf fmt "[sat] I assume a skolem %a@." E.print f

        | E.Let _ ->
          fprintf fmt "[sat] I assume a let-In %a@." E.print f

        | E.Iff _ ->
          fprintf fmt "[sat] I assume an equivalence %a@." E.print f

        | E.Xor _ ->
          fprintf fmt "[sat] I assume an neg-equivalence/Xor %a@." E.print f

      end

    let simplified_form f f' =
      if debug_sat () && verbose () then begin
        fprintf fmt "[sat] Simplified form of: %a@." E.print f;
        fprintf fmt "  is: %a@." FF.print f';
      end

    (* unused --
       let cnf_form f unit non_unit =
       if debug_sat () && verbose () then begin
        fprintf fmt "[sat] CFF form of: %a@." FF.print f;
        fprintf fmt "  is:@.";
        List.iter
          (List.iter (fun a -> fprintf fmt "UNIT: %a@." Atom.pr_atom a))
          unit;
        List.iter
          (fun c ->
             fprintf fmt "CLAUSE: ";
             List.iter (fun a -> fprintf fmt "%a or " Atom.pr_atom a) c;
             fprintf fmt "@."
          )non_unit
       end
    *)

    let model env =
      if debug_sat () then
        let model = SAT.boolean_model env.satml in
        eprintf "@.(2) satML's model:@.";
        List.iter
          (fun a ->
             eprintf " %f | %a @."
               (Atom.weight a)
               Atom.pr_atom a;
          ) (List.rev model);
        eprintf "  --------------@."

    let new_instances mode env =
      if debug_sat () then begin
        eprintf "@.# [sat] I GENERATE NEW INSTANCES (%s)#################@.@."
          mode;
        eprintf "(1) ground problem: @.";
        FF.Map.iter (fun f (md, _) ->
            eprintf "-> %d : %a@." md FF.print f) env.conj;
        fprintf fmt "@.Gamma:@.";
        model env;
      end

    (* unused --
       let generated_instances l =
       if verbose () && debug_sat () then begin
        eprintf "[new_instances] %d generated@." (List.length l);
        List.iter (fun { E.ff = f; origin_name; _ } ->
            eprintf " instance(origin = %s): %a@." origin_name E.print f;
          ) l
       end
    *)

    (* unused --
       let trivial_fact p inst =
       if verbose () && debug_sat () then begin
        if inst then eprintf "already known instance: %a@." E.print p
        else eprintf "already known skolem: %a@." E.print p
       end
    *)

    (* unused --
       let generated_skolems l =
       if verbose () && debug_sat () then begin
        eprintf "[new_skolems] %d generated@." (List.length l);
        List.iter (fun { E.ff = f; _ } -> eprintf " skolem: %a@." E.print f) l
       end
    *)

    let atoms_from_sat_branch f =
      if verbose () && debug_sat () then begin
        fprintf fmt "[extract_and_add_terms from] %a@." FF.print f;
      end

    let add_terms_of src terms =
      if verbose () && debug_sat () then begin
        fprintf fmt "[%s] add_terms_of:@." src;
        SE.iter (fprintf fmt ">> %a@." E.print) terms;
        fprintf fmt "@.";
      end

    (* unused --
       let axiom_def f =
       if debug_sat () then
        eprintf "[sat] I assume an axiom: %a@.@." E.print f
    *)

    let internal_axiom_def f a at =
      if debug_sat () then begin
        eprintf "[sat] I assume an internal axiom: %a <-> %a@."
          E.print a E.print f;
        fprintf fmt "at of a is %a@.@." Atom.pr_atom at
      end

    (* unused --
       let in_mk_theories_instances () =
       if Options.debug_fpa() > 0 || debug_sat() then
        fprintf fmt "@.[sat] entering mk_theories_instances:@."
    *)

    (* unused --
       let out_mk_theories_instances normal_exit =
       if Options.debug_fpa() > 0 || debug_sat() then
        if normal_exit then
          fprintf fmt "@.[sat] normal exit of mk_theories_instances.@.@."
        else
          fprintf fmt "@.exit mk_theories_instances with Inconsistency.@.@."
    *)

    let print_f_conj fmt hyp =
      match hyp with
      | [] -> fprintf fmt "True";
      | e::l ->
        fprintf fmt "%a" E.print e;
        List.iter (fun f -> fprintf fmt " /\\  %a" E.print f) l

    let print_theory_instance hyp gf =
      if Options.debug_fpa() > 1 || Options.debug_sat() then begin
        fprintf fmt "@.%s >@." (E.name_of_lemma_opt gf.E.lem);
        fprintf fmt "  hypotheses: %a@." print_f_conj hyp;
        fprintf fmt "  conclusion: %a@." E.print gf.E.ff;
      end

  end
  (*BISECT-IGNORE-END*)


  let print_propositional_model env =
    let model = SAT.boolean_model env.satml in
    fprintf fmt "Propositional:";
    List.iter
      (fun at ->
         (fprintf fmt "\n %a" E.print) (Atom.literal at)
      ) model;
    fprintf fmt "\n@."

  let print_model ~header fmt env =
    Format.print_flush ();
    if header then fprintf fmt "\nModel\n@.";
    print_propositional_model env;
    Th.print_model fmt (SAT.current_tbox env.satml)

  let make_explanation _ = Ex.empty
  (*
    if debug_sat () then
    fprintf fmt "make_explanation of %d clauses@." (List.length lc);
    List.fold_left
    (fun ex ({ST.form = f} as c) ->
    if debug_sat () then
    fprintf fmt "unsat_core: %a@." Atom.pr_clause c;
    Ex.union (Ex.singleton (Ex.Dep f)) ex
    )Ex.empty lc*)

  let selector env f orig =
    (Options.cdcl_tableaux () || not (ME.mem f env.gamma))
    && begin match E.form_view orig with
      | E.Lemma _ -> env.add_inst orig
      | E.Unit _ | E.Clause _ | E.Literal _ | E.Skolem _
      | E.Let _ | E.Iff _ | E.Xor _ -> true
      | E.Not_a_form -> assert false
    end

  (* <begin> copied from sat_solvers.ml *)

  let reduce_filters acc (hyp, gf, dep) =
    Debug.print_theory_instance hyp gf;
    let clause =
      List.fold_left
        (fun tmp f ->
           (* we cannot reduce like in DfsSAT *)
           E.mk_or (E.neg f) tmp false 0
        )gf.E.ff hyp
    in
    ({gf with E.ff=clause}, dep) :: acc

  let mk_theories_instances do_syntactic_matching _remove_clauses env acc =
    let t_match = Inst.matching_terms_info env.inst in
    let tbox = SAT.current_tbox env.satml in
    let _tbox, l =
      Th.theories_instances
        ~do_syntactic_matching t_match tbox (selector env) env.nb_mrounds 0
        [@ocaml.ppwarning "TODO: modifications made in tbox are lost! improve?"]
    in
    List.fold_left reduce_filters acc l, (match l with [] -> false | _ -> true)

  let syntactic_th_inst remove_clauses env acc =
    mk_theories_instances true remove_clauses env acc

  let semantic_th_inst_rec =
    let rec aux_rec remove_clauses env rnd acc =
      let acc, inst_made = mk_theories_instances false remove_clauses env acc in
      if not inst_made || rnd <= 1 then acc
      else aux_rec remove_clauses env (rnd - 1) acc
    in
    fun remove_clauses env rnd acc ->
      aux_rec remove_clauses env rnd acc

  let mk_theories_inst_rec env rnd =
    let acc, _ = syntactic_th_inst false env [] in
    semantic_th_inst_rec false env rnd acc

  (* <end> copied from sat_solvers.ml *)


  let literals_of_ex ex =
    Ex.fold_atoms
      (fun e acc ->
         match e with
         | Ex.Literal a -> a :: acc
         | Ex.Dep _ | Ex.RootDep _ -> acc
         (* for debug/profiling/proofs, ignore them *)
         | Ex.Bj _ | Ex.Fresh _ -> assert false
      ) ex []

  let mround menv env acc =
    let tbox = SAT.current_tbox env.satml in
    let gd2, ngd2 =
      Inst.m_predicates menv env.inst tbox (selector env) env.nb_mrounds
    in
    let l2 = List.rev_append (List.rev gd2) ngd2 in
    if Options.profiling() then Profiling.instances l2;
    (*let env = assume env l2 in*)
    let gd1, ngd1 =
      Inst.m_lemmas menv env.inst tbox (selector env) env.nb_mrounds
    in
    let l1 = List.rev_append (List.rev gd1) ngd1 in
    if Options.profiling() then Profiling.instances l1;
    let l = ((List.rev_append l2 l1) : (E.gformula * Explanation.t) list) in

    let th_insts = mk_theories_inst_rec env 10 in
    let l = List.rev_append th_insts l in
    List.fold_left
      (fun acc (gf, dep) ->
         match literals_of_ex dep with
         | []  ->
           gf :: acc
         | [{ Atom.lit; _ }] ->
           {gf with
            E.ff =
              E.mk_or gf.E.ff (E.neg lit) false 0} :: acc
         | _   -> assert false
      )acc l


  let factorize_iff a_t f =
    if E.equal a_t f then E.vrai
    else if E.equal (E.neg a_t) f then E.faux
    else match E.form_view f with
      | E.Iff(f1, f2) ->
        if E.equal f1 a_t then f2
        else if E.equal f2 a_t then f1
        else assert false
      | E.Not_a_form | E.Unit _ | E.Clause _ | E.Xor _
      | E.Literal _ | E.Lemma _ | E.Skolem _ | E.Let _ ->
        assert false

  let pred_def env f name dep _loc =
    (* dep currently not used. No unsat-cores in satML yet *)
    Debug.pred_def f;
    let a_t = E.mk_term (Symbols.name name) [] Ty.Tbool in
    if not (SE.mem a_t (E.max_ground_terms_rec_of_form f)) then
      {env with inst = Inst.add_predicate env.inst (mk_gf f) dep}
    else
      begin
        assert (not (ME.mem a_t env.ground_preds));
        let f_simpl = factorize_iff a_t f in
        (* a_t <-> f_simpl *)
        let not_a_t = E.neg a_t in
        let a_imp = E.mk_or not_a_t f_simpl false 0 in
        let not_a_imp = E.mk_or a_t (E.neg f_simpl) false 0 in
        let gp = ME.add a_t (mk_gf a_imp, dep) env.ground_preds in
        let gp = ME.add not_a_t (mk_gf not_a_imp, dep) gp in
        {env with ground_preds = gp}
      end

  let axiom_def env gf ex =
    {env with inst = Inst.add_lemma env.inst gf ex}

  let internal_axiom_def ax a at inst =
    Debug.internal_axiom_def ax a at;
    let gax = mk_gf ax in
    let ex = Ex.singleton (Ex.Literal at) in
    Inst.add_lemma inst gax ex

  let register_abstraction (env, new_abstr_vars) (f, (af, at)) =
    if debug_sat () && verbose () then
      fprintf fmt "abstraction of %a is %a@.@." E.print f FF.print af;
    let lat = Atom.literal at in
    let new_abstr_vars =
      if not (Atom.is_true at) then at :: new_abstr_vars else new_abstr_vars
    in
    assert (not (ME.mem f env.abstr_of_axs));
    assert (not (ME.mem lat env.axs_of_abstr));
    let env =
      if Atom.eq_atom at Atom.vrai_atom || Atom.eq_atom at Atom.faux_atom
      then
        env
      else
        { env with
          abstr_of_axs = ME.add f (af, at) env.abstr_of_axs;
          axs_of_abstr = ME.add lat (f, at) env.axs_of_abstr }
    in
    if Atom.level at = 0 then (* at is necessarily assigned if lvl = 0 *)
      if Atom.is_true at then
        axiom_def env (mk_gf f) Ex.empty, new_abstr_vars
      else begin
        assert (Atom.is_true (Atom.neg at));
        assert false (* FF.simplify invariant: should not happen *)
      end
    else begin
      (* FF.simplify invariant: should not happen *)
      assert (Atom.level at < 0);
      let ded = match E.neg f |> E.form_view with
        | E.Skolem q -> E.skolemize q
        | E.Unit _ | E.Clause _ | E.Literal _ | E.Lemma _
        | E.Let _ | E.Iff _ | E.Xor _ | E.Not_a_form -> assert false
      in
      (*XXX TODO: internal skolems*)
      let f = E.mk_or lat ded false 0 in
      let nlat = E.neg lat in
      (* semantics: nlat ==> f *)
      {env with skolems = ME.add nlat (mk_gf f) env.skolems},
      new_abstr_vars
    end

  let expand_skolems env acc sa =
    List.fold_left
      (fun acc a ->
         if verbose () then
           fprintf fmt "expand skolem of %a@.@." E.print a;
         try
           let { E.ff = f; _ } as gf = ME.find a env.skolems in
           if not (Options.cdcl_tableaux ()) &&
              ME.mem f env.gamma then acc
           else gf :: acc
         with Not_found -> acc
      ) acc sa

  let inst_env_from_atoms env acc sa =
    List.fold_left
      (fun (inst, acc) a ->
         let gf = mk_gf E.vrai in
         if verbose () then
           fprintf fmt "terms_of_atom %a @.@." E.print a;
         let inst = Inst.add_terms inst (E.max_ground_terms_of_lit a) gf in
         (* ax <-> a, if ax exists in axs_of_abstr *)
         try
           let ax, at = ME.find a env.axs_of_abstr in
           internal_axiom_def ax a at inst, acc
         with Not_found -> inst, acc
      ) (env.inst, acc) sa

  let measure at =
    Atom.level  at,
    Atom.weight at,
    Atom.index  at

  (* smaller is more important *)
  let cmp_tuples (l1, w1, i1) (l2,w2, i2) =
    (* lower decision level is better *)
    let res = compare l1 l2 in
    if res <> 0 then res
    else
      (* higher weight is better hence compare w2 w1 *)
      let res = Pervasives.compare w2 w1 in
      if res <> 0 then res
      else
        (* lower index is better *)
        compare i1 i2

  let max a b = if cmp_tuples a b > 0 then a else b

  (* unused --
     let take_max aux l =
     let ((lvl, _, ind) ,_) as acc =
      List.fold_left (fun ((mz,_) as acc) f ->
          match aux f with
          | None -> acc
          | Some (m, l) ->
            if cmp_tuples m mz > 0 then (m, l) else acc
        )((-1, -.1., -1), []) l
     in
     if lvl = -1 && ind = -1 then None
     else Some acc
  *)

  (* unused --
     let take_min aux l =
     let ((lvl, _, ind) ,_) as acc =
      List.fold_left (fun ((mz,_) as acc) f ->
          match aux f with
          | None -> acc
          | Some (m, l) ->
            if cmp_tuples m mz < 0 then (m, l) else acc
        )((max_int, -.1., max_int), []) l
     in
     if lvl = max_int && ind = max_int then None
     else Some acc
  *)

  let rec take_normal aux l =
    match l with
      [] -> None
    | a::l ->
      match aux a with
      | None -> take_normal aux l
      | (Some _) as v -> v

  let atoms_from_sat_branches =
    let rec atoms_from_sat_branch f =
      match FF.view f with
      | FF.UNIT at ->
        if not (Atom.is_true at) then None
        else Some (measure at, [Atom.literal at])

      | FF.AND l ->
        begin
          try
            let acc =
              List.fold_left (fun (mz,lz) f ->
                  match atoms_from_sat_branch f with
                  | None -> raise Exit
                  | Some (m, l) -> max m mz, List.rev_append l lz
                )((-1, -.1., -1), []) l
            in
            Some acc
          with Exit -> None
        end

      | FF.OR l ->
        take_normal atoms_from_sat_branch l
    in
    fun env ->
      FF.Map.fold
        (fun f _ sa ->
           Debug.atoms_from_sat_branch f;
           match atoms_from_sat_branch f with
           | None   -> assert false
           | Some (_,l) -> List.fold_left (fun sa a -> SE.add a sa) sa l
        ) env.conj SE.empty

  module SA = Satml_types.Atom.Set

  let atoms_from_lazy_sat =
    let rec add_reasons_graph _todo _done =
      match _todo with
        [] -> _done
      | a::_todo ->
        if SA.mem a _done then add_reasons_graph _todo _done
        else
          let _todo =
            List.fold_left
              (fun _todo a -> (Atom.neg a) :: _todo)
              _todo (Atom.reason_atoms a)
          in
          add_reasons_graph _todo (SA.add a _done)
    in
    fun ~frugal env ->
      let sa = SAT.instantiation_context env.satml env.ff_hcons_env in
      let sa =
        if frugal then sa
        else add_reasons_graph (SA.elements sa) SA.empty
      in
      SA.fold (fun a s -> SE.add (Atom.literal a) s) sa SE.empty

  let atoms_from_lazy_greedy env =
    let aux accu ff =
      let sf =
        try FF.Map.find ff env.conj |> snd
        with Not_found ->
          if FF.equal ff FF.vrai then SE.empty
          else begin
            fprintf fmt "%a not found in env.conj@." FF.print ff;
            assert false
          end
      in
      SE.fold (E.atoms_rec_of_form ~only_ground:false) sf accu
    in
    let accu =
      FF.Map.fold
        (fun ff _ accu -> aux accu ff)
        (SAT.known_lazy_formulas env.satml) SE.empty
    in
    SE.union (atoms_from_lazy_sat ~frugal:true env)
      (*otherwise, we loose atoms that abstract internal axioms *)
      (aux accu FF.vrai)
      [@ocaml.ppwarning
        "improve terms / atoms extraction in lazy/non-lazy \
         and greedy/non-greedy mode. Separate atoms from terms !"]

  let atoms_from_bmodel env =
    ME.fold (fun f _ sa -> (E.atoms_rec_of_form ~only_ground:false) f sa)
      env.gamma SE.empty

  let instantiation_context env ~greedy_round ~frugal =
    let sa = match greedy_round || greedy (), cdcl_tableaux_inst () with
      | false, false -> atoms_from_sat_branches env
      | false, true  -> atoms_from_lazy_sat ~frugal env
      | true , false -> atoms_from_bmodel env
      | true,  true  -> atoms_from_lazy_greedy env
    in
    SE.elements sa
      [@ocaml.ppwarning "Issue for greedy: terms inside lemmas not extracted"]

  let terms_from_dec_proc env =
    let terms = Th.extract_ground_terms (SAT.current_tbox env.satml) in
    Debug.add_terms_of "terms_from_dec_proc" terms;
    let gf = mk_gf E.vrai in
    Inst.add_terms env.inst terms gf

  let instantiate_ground_preds env acc sa =
    List.fold_left
      (fun acc a ->
         try (fst (ME.find a env.ground_preds)) :: acc
         with Not_found -> acc
      )acc sa
      [@ocaml.ppwarning "!!! Possibles issues du to replacement of atoms \
                         that are facts with TRUE by mk_lit (and simplify)"]


  let new_instances use_cs env sa acc =
    let inst, acc = inst_env_from_atoms env acc sa in
    let inst = terms_from_dec_proc {env with inst=inst} in
    mround use_cs {env with inst = inst} acc


  type pending = {
    seen_f : SE.t;
    activate : Atom.atom option FF.Map.t;
    new_vars : Atom.var list;
    unit : Atom.atom list list;
    nunit : Atom.atom list list;
    new_abstr_vars : Atom.atom list;
    updated : bool;
  }

  let pre_assume (env, acc) gf =
    let { E.ff = f; _ } = gf in
    if debug_sat() then
      fprintf fmt "Entry of pre_assume: Given %a@.@." E.print f;
    if SE.mem f acc.seen_f then env, acc
    else
      let acc = {acc with seen_f = SE.add f acc.seen_f} in
      try
        let _, ff = ME.find f env.gamma in
        match ff with
        | None    ->
          env, acc
            [@ocaml.ppwarning "TODO: should be assert failure?"]

        | Some ff ->
          if SAT.exists_in_lazy_cnf env.satml ff then env, acc
          else
            env,
            {acc with
             activate = FF.Map.add ff None acc.activate;
             updated = true}
      with Not_found ->
        Debug.assume gf;
        match E.form_view f with
        | E.Lemma _ ->
          let ff = FF.vrai in
          let _, old_sf =
            try FF.Map.find ff env.conj with Not_found -> 0, SE.empty
          in
          let env =
            {env with
             gamma = ME.add f (env.nb_mrounds, None)  env.gamma;
             conj  = FF.Map.add ff (env.nb_mrounds, SE.add f old_sf) env.conj }
          in
          (* This assert is not true assert (dec_lvl = 0); *)
          axiom_def env gf Ex.empty, {acc with updated = true}

        | E.Not_a_form -> assert false
        | E.Unit _ | E.Clause _ | E.Literal _ | E.Skolem _
        | E.Let _ | E.Iff _ | E.Xor _ ->
          let ff, axs, new_vars =
            FF.simplify env.ff_hcons_env f
              (fun f -> ME.find f env.abstr_of_axs) acc.new_vars
          in
          let acc = {acc with new_vars = new_vars} in
          let cnf_is_in_cdcl = FF.Map.mem ff env.conj in
          let _, old_sf =
            try FF.Map.find ff env.conj with Not_found -> 0, SE.empty
          in
          let env =
            {env with
             gamma = ME.add f (env.nb_mrounds, Some ff) env.gamma;
             conj  = FF.Map.add ff (env.nb_mrounds, SE.add f old_sf) env.conj }
          in
          Debug.simplified_form f ff;
          let env, new_abstr_vars =
            List.fold_left register_abstraction (env, acc.new_abstr_vars) axs
          in
          let acc = { acc with new_abstr_vars } in

          if FF.equal ff FF.vrai then env, acc
          else
          if cnf_is_in_cdcl then
            (* this means that there exists another E.t that is
               equivalent to f. These two formulas have the same ff *)
            if SAT.exists_in_lazy_cnf env.satml ff then env, acc
            else
              env,
              {acc with
               activate = FF.Map.add ff None acc.activate;
               updated = true}
          else
            let ff_abstr,new_proxies,proxies_mp, new_vars =
              FF.cnf_abstr env.ff_hcons_env ff env.proxies acc.new_vars
            in
            let env = {env with proxies = proxies_mp} in
            let nunit =
              List.fold_left FF.expand_proxy_defn acc.nunit new_proxies
            in
            let acc =
              {acc with
               new_vars;
               nunit;
               unit = [ff_abstr] :: acc.unit;
               activate = FF.Map.add ff None acc.activate;
               updated = true
              }
            in
            env, acc

  let cdcl_assume env pending ~dec_lvl =
    let { seen_f; activate; new_vars; unit; nunit; updated; _ } = pending in
    (*
    fprintf fmt "pending : %d distinct forms@." (SE.cardinal seen_f);
    fprintf fmt "pending : %d to activate@." (SFF.cardinal activate);
    fprintf fmt "pending : %d new vars@." (List.length new_vars);
    fprintf fmt "pending : %d unit cnf@." (List.length unit);
    fprintf fmt "pending : %d non-unit cnf@." (List.length nunit);
    fprintf fmt "pending : updated = %b@." updated;
    *)
    if SE.is_empty seen_f then begin
      assert (FF.Map.is_empty activate);
      assert (new_vars == []);
      assert (unit == []);
      assert (nunit == []);
      assert (not updated);
    end
    else
      try
        let f = E.vrai
            [@ocaml.ppwarning "TODO: should fix for unsat cores generation"]
        in
        SAT.set_new_proxies env.satml env.proxies;
        let nbv = FF.nb_made_vars env.ff_hcons_env in
        let unit, nunit = SAT.new_vars env.satml ~nbv new_vars unit nunit in
        (*update_lazy_cnf done inside assume at the right place *)
        (*SAT.update_lazy_cnf activate ~dec_lvl;*)
        SAT.assume env.satml unit nunit f ~cnumber:0 activate ~dec_lvl;
      with
      | Satml.Unsat (lc)  -> raise (IUnsat (env, make_explanation lc))
      | Satml.Sat -> assert false


  let assume_aux_bis ~dec_lvl env l =
    let pending = {
      seen_f = SE.empty; activate = FF.Map.empty;
      new_vars = []; unit = []; nunit = []; updated = false;
      new_abstr_vars = [];
    }
    in
    (*fprintf fmt "@.assume aux: %d@." (List.length l);*)
    let env, pending = List.fold_left pre_assume (env, pending) l in
    cdcl_assume env pending ~dec_lvl;
    env, pending.updated, pending.new_abstr_vars


  let rec assume_aux ~dec_lvl env l =
    let env, updated, new_abstr_vars = assume_aux_bis ~dec_lvl env l in
    let bot_abstr_vars = (* try to immediately expand newly added skolems *)
      List.fold_left (fun acc at ->
          let neg_at = Atom.neg at in
          if Atom.is_true neg_at then (Atom.literal neg_at) :: acc else acc
        )[] new_abstr_vars
    in
    match bot_abstr_vars with
    | [] -> env, updated
    | _ ->
      let res = expand_skolems env [] bot_abstr_vars in
      if res == [] then env, updated
      else
        let env, updated' = assume_aux ~dec_lvl env res in
        env, updated || updated'


  let frugal_mconf () =
    {Util.nb_triggers = nb_triggers ();
     no_ematching = no_Ematching();
     triggers_var = triggers_var ();
     use_cs = false;
     backward = Util.Normal;
     greedy = greedy ();
    }

  let normal_mconf () =
    {Util.nb_triggers = Pervasives.max 2 (nb_triggers () * 2);
     no_ematching = no_Ematching();
     triggers_var = triggers_var ();
     use_cs = false;
     backward = Util.Normal;
     greedy = greedy ();
    }

  let greedy_mconf () =
    {Util.nb_triggers = Pervasives.max 10 (nb_triggers () * 10);
     no_ematching = false;
     triggers_var = true;
     use_cs = true;
     backward = Util.Normal;
     greedy = true;
    }

  let do_instantiation env sa mconf msg ~dec_lvl =
    Debug.new_instances msg env;
    let l = instantiate_ground_preds env [] sa in
    let l = expand_skolems env l sa in
    let l = new_instances mconf env sa l in
    let env, updated = assume_aux ~dec_lvl env l in
    env, updated

  type instantiation_strat =
    | Auto
    | Force_normal
    | Force_greedy


  let instantiation env inst_strat dec_lvl =
    let nb_mrounds = env.nb_mrounds in
    match inst_strat with
    | Force_normal ->
      let mconf = frugal_mconf () in (* take frugal_mconf if normal is forced *)
      let env = {env with last_forced_normal = nb_mrounds} in
      let sa = instantiation_context env ~greedy_round:false ~frugal:false in
      do_instantiation env sa mconf "normal-inst (forced)" ~dec_lvl

    | Force_greedy ->
      let mconf = normal_mconf () in (*take normal_mconf if greedy is forced*)
      let env = {env with last_forced_greedy = nb_mrounds} in
      let sa = instantiation_context env ~greedy_round:true ~frugal:false in
      do_instantiation env sa mconf "greedy-inst (forced)" ~dec_lvl

    | Auto ->
      List.fold_left
        (fun ((env, updated) as acc) (mconf, debug, greedy_round, frugal) ->
           if updated then acc
           else
             let sa = instantiation_context env ~greedy_round ~frugal in
             do_instantiation env sa mconf debug ~dec_lvl
        )(env, false)
        [ frugal_mconf (), "frugal-inst", false, true ;
          normal_mconf (), "normal-inst", false, false;
          greedy_mconf (), "greedy-inst", true , false ]


  let rec unsat_rec env ~first_call:_ : unit =
    try SAT.solve env.satml; assert false
    with
    | Satml.Unsat lc -> raise (IUnsat (env, make_explanation lc))
    | Satml.Sat ->
      try
        (*if first_call then SAT.cancel_until 0;*)
        let env = {env with nb_mrounds = env.nb_mrounds + 1}
            [@ocaml.ppwarning
              "TODO: first intantiation a la DfsSAT before searching ..."]
        in
        if Options.profiling() then Profiling.instantiation env.nb_mrounds;
        let strat =
          if env.nb_mrounds - env.last_forced_greedy > 1000 then Force_greedy
          else
          if env.nb_mrounds - env.last_forced_normal > 50 then Force_normal
          else Auto
        in
        (*let strat = Auto in*)
        let dec_lvl = SAT.decision_level env.satml in
        let env, updated = instantiation env strat dec_lvl in
        let env, updated =
          if not updated && strat != Auto then instantiation env Auto dec_lvl
          else env, updated
        in
        let dec_lvl' = SAT.decision_level env.satml in
        let env =
          if strat == Auto && dec_lvl' = dec_lvl then
            (* increase chances of forcing Normal each time Auto
               instantiation doesn't allow to backjump *)
            {env with last_forced_normal = env.last_forced_normal - 1}
          else
            env
        in
        if not updated then raise (I_dont_know env);
        unsat_rec env ~first_call:false

      with Ex.Inconsistent (expl, _cls) -> (*may be raised during matching*)
      try
        SAT.conflict_analyze_and_fix env.satml (Satml.C_theory expl);
        unsat_rec env ~first_call:false
      with
      | Satml.Unsat lc -> raise (IUnsat (env, make_explanation lc))
      | _ -> assert false


  (* copied from sat_solvers.ml *)
  let max_term_depth_in_sat env =
    let aux mx f = Pervasives.max mx (E.depth f) in
    let max_t = ME.fold (fun f _ mx -> aux mx f) env.gamma 0 in
    ME.fold (fun _ ({ E.ff = f; _ }, _) mx -> aux mx f) env.ground_preds max_t


  let checks_implemented_features () =
    let fails msg =
      Format.eprintf
        "Currently, %S feature is not implemented in CDCL solver !@."
        msg;
      Format.eprintf
        "Please use the old Tableaux-like SAT solver unstead.@.";
      exit 1
    in
    let open Options in
    if interpretation () <> 0 then fails "interpretation";
    if save_used_context () then fails "save_used_context";
    if unsat_core () then fails "unsat_core";
    if all_models () then fails "all_models";
    if model () then fails "model"


  let unsat env gf =
    checks_implemented_features ();
    Debug.unsat gf;
    (*fprintf fmt "FF.unsat@.";*)
    (* In dfs_sat goals' terms are added to env.inst *)
    let env =
      {env with inst =
                  Inst.add_terms env.inst
                    (E.max_ground_terms_rec_of_form gf.E.ff) gf}
    in
    try
      assert (SAT.decision_level env.satml == 0);
      let env, _updated = assume_aux ~dec_lvl:0 env [gf] in
      let max_t = max_term_depth_in_sat env in
      let env = {env with inst = Inst.register_max_term_depth env.inst max_t} in
      unsat_rec env ~first_call:true;
      assert false
    with IUnsat (_env, dep) ->
      assert begin
        Ex.fold_atoms
          (fun e b -> match e with
             | Ex.Bj _ -> false (* only used in fun_sat *)
             | Ex.Literal _ | Ex.Fresh _ -> false (* bug if this happens *)
             | Ex.RootDep _ | Ex.Dep _ -> b
          )dep true
      end;
      dep

  let assume env gf _dep =
    (* dep currently not used. No unsat-cores in satML yet *)
    assert (SAT.decision_level env.satml == 0);
    try fst (assume_aux ~dec_lvl:0 env [gf])
    with IUnsat (_env, dep) -> raise (Unsat dep)

  (* instrumentation of relevant exported functions for profiling *)
  let assume t ff dep =
    if not (Options.timers ()) then assume t ff dep
    else
      try
        Timers.exec_timer_start Timers.M_Sat Timers.F_assume;
        let t = assume t ff dep in
        Timers.exec_timer_pause Timers.M_Sat Timers.F_assume;
        t
      with exn ->
        Timers.exec_timer_pause Timers.M_Sat Timers.F_assume;
        raise exn

  let unsat t ff =
    if not (Options.timers()) then unsat t ff
    else
      try
        Timers.exec_timer_start Timers.M_Sat Timers.F_unsat;
        let t = unsat t ff in
        Timers.exec_timer_pause Timers.M_Sat Timers.F_unsat;
        t
      with exn ->
        Timers.exec_timer_pause Timers.M_Sat Timers.F_unsat;
        raise exn

  let assume_th_elt env th_elt dep =
    SAT.assume_th_elt env.satml th_elt dep;
    env

end

(*
(*+ no dynamic loading of SAT solvers anymore +*)
let () = Sat_solver.set_current (module Main : Sat_solver_sig.S)
*)
