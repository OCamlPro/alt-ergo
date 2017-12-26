(******************************************************************************)
(*                                                                            *)
(*     Alt-Ergo: The SMT Solver For Software Verification                     *)
(*     Copyright (C) 2013-2017 --- OCamlPro SAS                               *)
(*                                                                            *)
(*     This file is distributed under the terms of the license indicated      *)
(*     in the file 'License.OCamlPro'. If 'License.OCamlPro' is not           *)
(*     present, please contact us to clarify licensing.                       *)
(*                                                                            *)
(******************************************************************************)

module Main : Sat_solver_sig.S = struct

  open Options
  open Format
  module Th = Theory.Main

  module SAT = Satml.Make(Th)
  module Inst = Instances.Make(Th)
  module Ex = Explanation
  module F = Formula
  module MF = F.Map
  module SF = F.Set
  module A = Literal.LT
  module MA = A.Map
  module Types = Satml.Types

  module FF = Satml.Flat_Formula
  module MFF = FF.Map

  let reset_refs () = SAT.reset_steps ()
  let get_steps () = SAT.get_steps ()

  type t = {
    nb_mrounds : int;
    gamma : (int * FF.t option) MF.t;
    conj : (int * SF.t) MFF.t;
    abstr_of_axs : (FF.t * Types.atom) MF.t;
    axs_of_abstr : F.t MA.t;
    proxies : (Types.atom * Types.atom list * bool) Util.MI.t;
    inst : Inst.t;
    ground_preds : F.gformula A.Map.t; (* key <-> f *)
    skolems : F.gformula A.Map.t; (* key <-> f *)
    add_inst: Formula.t -> bool;
  }

  let empty () =
    SAT.empty (); (*(* Soundness issue due to bad hash-consing *) *)
    { gamma = MF.empty;
      nb_mrounds = 0;
      conj = MFF.empty;
      abstr_of_axs = MF.empty;
      axs_of_abstr = MA.empty;
      proxies = Util.MI.empty;
      inst = Inst.empty;
      ground_preds = A.Map.empty;
      skolems = A.Map.empty;
      add_inst = fun _ -> true;
    }

  let empty_with_inst add_inst =
    { (empty ()) with add_inst = add_inst }

  exception Sat of t
  exception Unsat of Explanation.t
  exception I_dont_know of t

  exception IUnsat of t * Explanation.t

  let mk_gf f =
    { F.f = f;
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

  module Replay = struct

    let print_gamma env =
      fprintf fmt "(* ground problem *)@.";
      MF.iter (fun f _ -> fprintf fmt "%a -> @." F.print f) env.gamma;
      fprintf fmt "false@."

    let replay_with_dfs env =
      try
        let env_dfs =
          try
            let env_dfs =
              MF.fold
                (fun f _ env_dfs -> Fun_sat.assume env_dfs (mk_gf f))
                env.gamma (Fun_sat.empty ())
            in
            MF.fold
              (fun f (_,at) env_dfs ->
                let f = F.mk_iff f (F.mk_lit (Types.literal at) 0) 0 in
                Fun_sat.assume env_dfs (mk_gf f)
              ) env.abstr_of_axs env_dfs
          with Fun_sat.Unsat dep -> raise (Unsat dep)
        in
        ignore (Fun_sat.unsat env_dfs (mk_gf F.vrai));
        fprintf fmt "replay (by Fun_sat.unsat)@."

      with
        | Unsat _ ->
          fprintf fmt "replay (by Fun_sat.assume)@.";
        | Fun_sat.Unsat _ -> assert false
        | Fun_sat.Sat _ ->
          fprintf fmt "satML said UNSAT but Fun_sat said SAT@.";
          print_gamma env;
          exit 12
        | e ->
          fprintf fmt "satML said UNSAT but Fun_sat said:@.";
          (*fprintf fmt "%s@." (Printexc.to_string e);*)
          exit 13
  end

  (*BISECT-IGNORE-BEGIN*)
  module Debug = struct

    let pred_def f =
      if debug_sat () then
        eprintf "[sat] I assume a predicate: %a@.@." F.print f

    let unsat gf =
      if debug_sat () then
        printf "[sat] unsat of %a ?@." F.print gf.F.f

    let assume gf =
      let {F.f=f;age=age;lem=lem;mf=mf;from_terms=terms} = gf in
      if debug_sat () then begin
        match F.view f with
	  | F.Unit _ -> ()

	  | F.Clause _ ->
	    fprintf fmt "[sat] I assume a clause %a@." F.print f

	  | F.Lemma _ ->
	    fprintf fmt "[sat] I assume a [%d-atom] lemma: %a@."
              (F.size f) F.print f

	  | F.Literal a ->
	    Term.print_list str_formatter terms;
	    let s = flush_str_formatter () in
	    let n = match lem with
	      | None -> ""
	      | Some ff ->
	        (match F.view ff with F.Lemma xx -> xx.F.name | _ -> "")
	    in
	    fprintf fmt "\n[sat]I assume a literal (%s : %s) %a@]@."
              n s Literal.LT.print a;
	    fprintf fmt "================================================@.@."

	  | F.Skolem _ ->
	    fprintf fmt "[sat] I assume a skolem %a@." F.print f

	  | F.Let {F.let_var=lvar; let_term=lterm; let_f=lf} ->
	    fprintf fmt "[sat] I assume a let %a = %a in %a@."
	      Symbols.print lvar Term.print lterm F.print lf;
      end

    let simplified_form f f' =
      if debug_sat () && verbose () then begin
        fprintf fmt "[sat] Simplified form of: %a@." F.print f;
        fprintf fmt "  is: %a@." FF.print f';
      end

    let cnf_form f unit non_unit =
      if debug_sat () && verbose () then begin
        fprintf fmt "[sat] CFF form of: %a@." FF.print f;
        fprintf fmt "  is:@.";
        List.iter
          (List.iter (fun a -> fprintf fmt "UNIT: %a@." Types.pr_atom a))
          unit;
        List.iter
          (fun c ->
            fprintf fmt "CLAUSE: ";
            List.iter (fun a -> fprintf fmt "%a or " Types.pr_atom a) c;
            fprintf fmt "@."
          )non_unit
      end

    let model ()=
      if debug_sat () then
        let model = SAT.boolean_model () in
        eprintf "@.(2) satML's model:@.";
        List.iter
          (fun a ->
            eprintf " %f | %a @."
              (Types.weight a)
              Types.pr_atom a;
          ) (List.rev model);
        eprintf "  --------------@."

    let mround () =
      if debug_sat () then fprintf fmt "matching round@."

    let new_instances mode env =
      if debug_sat () then begin
        eprintf "@.# [sat] I GENERATE NEW INSTANCES (%s)#################@.@."
          mode;
        eprintf "(1) ground problem: @.";
        MFF.iter (fun f (md, _) ->
          eprintf "-> %d : %a@." md FF.print f) env.conj;
        fprintf fmt "@.Gamma:@.";
        model ();
      end

    let generated_instances l =
      if verbose () && debug_sat () then begin
        eprintf "[new_instances] %d generated@." (List.length l);
        List.iter (fun {F.f=f; origin_name; lem} ->
          eprintf " instance(origin = %s): %a@." origin_name F.print f;
        ) l
      end

    let trivial_fact p inst =
      if verbose () && debug_sat () then begin
        if inst then eprintf "already known instance: %a@." F.print p
        else eprintf "already known skolem: %a@." F.print p
      end

    let generated_skolems l =
      if verbose () && debug_sat () then begin
        eprintf "[new_skolems] %d generated@." (List.length l);
        List.iter (fun {F.f=f} -> eprintf " skolem: %a@." F.print f) l
      end

    let atoms_from_sat_branch f =
      if verbose () && debug_sat () then begin
        fprintf fmt "[extract_and_add_terms from] %a@." FF.print f;
      end

    let add_terms_of src terms =
      if verbose () && debug_sat () then begin
        fprintf fmt "[%s] add_terms_of:@." src;
        Term.Set.iter (fprintf fmt ">> %a@." Term.print) terms;
        fprintf fmt "@.";
      end

    let axiom_def f =
      if debug_sat () then
        eprintf "[sat] I assume an axiom: %a@.@." F.print f

    let internal_axiom_def f a =
      if debug_sat () then
        eprintf "[sat] I assume an internal axiom: %a <-> %a@.@."
          A.print a F.print f

    let in_mk_theories_instances () =
      if Options.debug_fpa() > 0 || debug_sat() then
        fprintf fmt "@.[sat] entering mk_theories_instances:@."

    let out_mk_theories_instances normal_exit =
      if Options.debug_fpa() > 0 || debug_sat() then
        if normal_exit then
          fprintf fmt "@.[sat] normal exit of mk_theories_instances.@.@."
        else
          fprintf fmt "@.exit mk_theories_instances with Inconsistency.@.@."

    let print_f_conj fmt hyp =
      match hyp with
      | [] -> fprintf fmt "True";
      | e::l ->
        fprintf fmt "%a" F.print e;
        List.iter (fun f -> fprintf fmt " /\\  %a" F.print f) l

    let print_theory_instance hyp gf =
      if Options.debug_fpa() > 1 || Options.debug_sat() then begin
        fprintf fmt "@.%s >@." (F.name_of_lemma_opt gf.F.lem);
        fprintf fmt "  hypotheses: %a@." print_f_conj hyp;
        fprintf fmt "  conclusion: %a@." F.print gf.F.f;
      end

  end
  (*BISECT-IGNORE-END*)


  let print_propositional_model () =
    let model = SAT.boolean_model () in
    fprintf fmt "Propositional:";
    List.iter
      (fun at ->
        (fprintf fmt "\n %a" Literal.LT.print) (Types.literal at)
      ) model;
    fprintf fmt "\n@."

  let print_model ~header fmt env =
    Format.print_flush ();
    if header then fprintf fmt "\nModel\n@.";
    print_propositional_model ();
    Th.print_model fmt (SAT.current_tbox ())

  let make_explanation lc = Ex.empty
  (*
    if debug_sat () then
    fprintf fmt "make_explanation of %d clauses@." (List.length lc);
    List.fold_left
    (fun ex ({ST.form = f} as c) ->
    if debug_sat () then
    fprintf fmt "unsat_core: %a@." Types.pr_clause c;
    Ex.union (Ex.singleton (Ex.Dep f)) ex
    )Ex.empty lc*)

  let selector env f orig =
    (lazy_sat () || not (MF.mem f env.gamma))
    && begin match F.view orig with
      | F.Lemma _ -> env.add_inst orig
      | _ -> true
    end

  (* <begin> copied from sat_solvers.ml *)

  let reduce_filters acc (hyp, gf, dep) =
    Debug.print_theory_instance hyp gf;
    let clause =
      List.fold_left
        (fun tmp f ->
          (* we cannot reduce like in DfsSAT *)
          F.mk_or (F.mk_not f) tmp false 0
        )gf.F.f hyp
    in
    ({gf with F.f=clause}, dep) :: acc

  let mk_theories_instances do_synt_ma remove_clauses env acc =
    let t_match = Inst.matching_terms_info env.inst in
    let tbox = SAT.current_tbox () in
    let tbox, l =
      Th.theories_instances
        do_synt_ma t_match tbox (selector env) env.nb_mrounds 0
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
        | Ex.Dep _ -> acc (* for debug/profiling/proofs, ignore them *)
        | Ex.Bj _ | Ex.Fresh _ -> assert false
      ) ex []

  let mround env acc =
    let tbox = SAT.current_tbox () in
    let gd2, ngd2 =
      Inst.m_predicates ~backward:Util.Normal
        env.inst tbox (selector env) env.nb_mrounds
    in
    let l2 = List.rev_append (List.rev gd2) ngd2 in
    if Options.profiling() then Profiling.instances l2;
    (*let env = assume env l2 in*)
    let gd1, ngd1 =
      Inst.m_lemmas ~backward:Util.Normal
        env.inst tbox (selector env) env.nb_mrounds
    in
    let l1 = List.rev_append (List.rev gd1) ngd1 in
    if Options.profiling() then Profiling.instances l1;
    let l = ((List.rev_append l2 l1) : (F.gformula * Explanation.t) list) in

    let th_insts = mk_theories_inst_rec env 10 in
    let l = List.rev_append th_insts l in
    List.fold_left
      (fun acc (gf, dep) ->
        match literals_of_ex dep with
        | []  ->
          gf :: acc
        | [a] ->
          {gf with F.f = F.mk_or gf.F.f (F.mk_lit (A.neg a) 0) false 0} :: acc
        | _   -> assert false
      )acc l


  let factorize_iff a_t f =
    let not_at = F.mk_not (F.mk_lit a_t 0) in
    match F.view f with
    | F.Unit(f1, f2) ->
      begin
        match F.view f1, F.view f2 with
        | F.Clause(g11, g12, _), F.Clause(g21, g22, _) ->
          let ng21 = F.mk_not g21 in
          let ng22 = F.mk_not g22 in
          assert (F.equal g11 ng21 || F.equal g11 ng22);
          assert (F.equal g12 ng21 || F.equal g12 ng22);
          if F.equal g21 not_at then g22
          else if F.equal ng21 not_at then F.mk_not g22
          else
            if F.equal g22 not_at then g21
            else if F.equal ng22 not_at then F.mk_not g21
            else assert false
        | _ -> assert false
      end
    | F.Literal a ->
      begin
        match Literal.LT.view a with
        | Literal.Pred (t, b) -> if b then F.faux else F.vrai
        | _ -> assert false
      end
    | _ -> assert false

  let pred_def env f name loc =
    Debug.pred_def f;
    let t = Term.make (Symbols.name name) [] Ty.Tbool in
    if not (Term.Set.mem t (F.ground_terms_rec f)) then
      {env with inst = Inst.add_predicate env.inst (mk_gf f)}
    else
      begin
        let a_t = A.mk_pred t false in
        assert (not (A.Map.mem a_t env.ground_preds));
        let f_simpl = factorize_iff a_t f in
        (* a_t <-> f_simpl *)
        let not_a_t = A.neg a_t in
        let a_imp = F.mk_or (F.mk_lit not_a_t 0) f_simpl false 0 in
        let not_a_imp = F.mk_or (F.mk_lit a_t 0) (F.mk_not f_simpl) false 0 in
        let gp = A.Map.add a_t (mk_gf a_imp) env.ground_preds in
        let gp = A.Map.add not_a_t (mk_gf not_a_imp) gp in
        {env with ground_preds = gp}
      end

  let axiom_def env gf ex =
    let inst, deds = Inst.add_lemma env.inst gf ex in
    {env with inst}, deds

  let internal_axiom_def ax a (inst, acc) =
    Debug.internal_axiom_def ax a;
    let gax = mk_gf ax in
    let ex = Ex.singleton (Ex.Literal a) in
    let inst, deds = Inst.add_lemma inst gax ex in
    let acc =
      List.fold_left (fun acc (gf, dep) ->
        let res = F.mk_or gf.F.f (F.mk_lit (A.neg a) 0) false 0 in
        {gf with F.f = res} :: acc
      )acc deds
    in
    inst, acc

  let register_abstraction (env, acc) (f, (af, at)) =
    if debug_sat () && verbose () then
      fprintf fmt "abstraction of %a is %a@.@." F.print f FF.print af;
    let lat = Types.literal at in
    assert (not (MF.mem f env.abstr_of_axs));
    assert (not (MA.mem lat env.axs_of_abstr));
    let env =
      if Types.eq_atom at Types.vrai_atom || Types.eq_atom at Types.faux_atom
      then
        env
      else
        { env with
          abstr_of_axs = MF.add f (af, at) env.abstr_of_axs;
          axs_of_abstr = MA.add lat f env.axs_of_abstr }
    in
    if Types.level at = 0 then (* at is necessarily assigned *)
      if Types.is_true at then
        let env, deds = axiom_def env (mk_gf f) Ex.empty in
        let acc =
          List.fold_left (fun acc (gf, ex) -> (gf(*, None*))::acc
            [@ocaml.ppwarning "TODO: is None OK ? analyze the situation ?"])
            acc deds
        in
        env, acc
      else
        let () = assert (Types.is_true (Types.neg at)) in

        (* these two asserts are here because this seems to be dead code.
           Should fix FF.simplify to enable it *)
        assert (not (Types.eq_atom at Types.vrai_atom));
        assert false; (* not present in old version *)
        let ded = match F.mk_not f |> F.view with
          | F.Skolem q -> F.skolemize q
          | _ -> assert false
        in
        (*(not f or at) is true, ie. (not f) is true bcs at is false *)
        (* ded's lazy should be added at level 0 --> add it dynamically. *)
        (* XXX: see warning at the end of the function *)
        env, (mk_gf ded(*, Some Types.faux_atom*)) :: acc
          [@ocaml.ppwarning "Lazy should be added at level 0 ! How ?"]
    else
      let ded = match F.mk_not f |> F.view with
        | F.Skolem q -> F.skolemize q
        | _ -> assert false
      in
      (*XXX TODO: internal skolems*)
      let f = F.mk_or (F.mk_lit lat 0) ded false 0 in
      let nlat = A.neg lat in
      assert (not (A.Map.mem nlat env.skolems));
      assert (not (A.Map.mem lat env.skolems));
      {env with skolems = A.Map.add nlat (mk_gf f) env.skolems}, acc
        [@ocaml.ppwarning "Lazy should be dynamic, attached to at ! But, what happends if at is true at level L and we are at level N > L ? information lost in lazy_cnf in case of backjump to a level M such that N > M > L"]


  let expand_skolems env acc sa =
    List.fold_left
      (fun acc a ->
        if verbose () then
          fprintf fmt "expand skolem of %a@.@." Literal.LT.print a;
        try
          let {F.f} as gf = A.Map.find a env.skolems in
          if not (lazy_sat ()) && MF.mem f env.gamma then acc
          else gf :: acc
        with Not_found -> acc
      ) acc sa

  let inst_env_from_atoms env acc sa =
    List.fold_left
      (fun (inst, acc) a ->
        let gf = mk_gf F.vrai in
        if verbose () then
          fprintf fmt "terms_of_atom %a @.@." Literal.LT.print a;
        let inst = Inst.add_terms inst (A.ground_terms a) gf in
        (* ax <-> a, if ax exists in axs_of_abstr *)
        try
          let ax = MA.find a env.axs_of_abstr in
          internal_axiom_def ax a (inst, acc)
        with Not_found -> inst, acc
      ) (env.inst, acc) sa

  let measure at =
    Types.level  at,
    Types.weight at,
    Types.index  at

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

  let take_max aux l =
    let ((lvl, _, ind) ,_) as acc =
      List.fold_left (fun ((mz,lz) as acc) f ->
        match aux f with
          | None -> acc
          | Some (m, l) ->
            if cmp_tuples m mz > 0 then (m, l) else acc
      )((-1, -.1., -1), []) l
    in
    if lvl = -1 && ind = -1 then None
    else Some acc

  let take_min aux l =
    let ((lvl, _, ind) ,_) as acc =
      List.fold_left (fun ((mz,lz) as acc) f ->
        match aux f with
          | None -> acc
          | Some (m, l) ->
            if cmp_tuples m mz < 0 then (m, l) else acc
      )((max_int, -.1., max_int), []) l
    in
    if lvl = max_int && ind = max_int then None
    else Some acc

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
          if not (Types.is_true at) then None
          else Some (measure at, [Types.literal at])

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
      MFF.fold
        (fun f _ sa ->
          Debug.atoms_from_sat_branch f;
          match atoms_from_sat_branch f with
          | None   -> assert false
          | Some (_,l) -> List.fold_left (fun sa a -> A.Set.add a sa) sa l
        ) env.conj A.Set.empty

  module SA = Set.Make (struct
    type t = Types.atom
    let compare = Types.cmp_atom
  end)

  let atoms_from_lazy_sat =
    let rec add_reasons_graph _todo _done =
      match _todo with
        [] -> _done
      | a::_todo ->
        if SA.mem a _done then add_reasons_graph _todo _done
        else
          let _todo =
            List.fold_left
              (fun _todo a -> (Types.neg a) :: _todo)
              _todo (Types.reason_atoms a)
          in
          add_reasons_graph _todo (SA.add a _done)
    in
    fun ~frugal env ->
      let sa =
        List.fold_left (fun accu l ->
          List.fold_left (fun accu (a,_,_) ->
            SA.add (Types.get_atom a) accu) accu l
        ) SA.empty (SAT.theory_assumed ())
      in
      let sa =
        if frugal then sa
        else add_reasons_graph (SA.elements sa) SA.empty
      in
      SA.fold (fun a s -> A.Set.add (Types.literal a) s) sa A.Set.empty

  let atoms_from_lazy_greedy env =
    let aux accu ff =
      let sf =
        try MFF.find ff env.conj |> snd
        with Not_found ->
          if FF.equal ff FF.vrai then SF.empty
          else begin
            fprintf fmt "%a not found in env.conj@." FF.print ff;
            assert false
          end
      in
      SF.fold (F.atoms_rec ~only_ground:false) sf accu
    in
    let accu =
      FF.Map.fold
        (fun ff _ accu -> aux accu ff)
        (SAT.known_lazy_formulas ()) A.Set.empty
    in
    A.Set.union (atoms_from_lazy_sat ~frugal:true env)
      (*otherwise, we loose atoms that abstract internal axioms *)
      (aux accu FF.vrai)
      [@ocaml.ppwarning "improve terms / atoms extraction in lazy/non-lazy and greedy/non-greedy mode. Separate atoms from terms !"]

  let atoms_from_bmodel env =
    MF.fold (fun f _ sa -> (F.atoms_rec ~only_ground:false) f sa)
      env.gamma A.Set.empty

  let atoms_from_sat_branches env ~greedy_round ~frugal =
    let sa = match greedy_round || greedy (), lazy_sat () with
      | false, false -> atoms_from_sat_branches env
      | false, true  -> atoms_from_lazy_sat ~frugal env
      | true , false -> atoms_from_bmodel env
      | true,  true  -> atoms_from_lazy_greedy env
    in
    A.Set.elements sa
      [@ocaml.ppwarning "Issue for greedy: terms inside lemmas not extracted"]

  let terms_from_dec_proc env =
    let terms = Th.extract_ground_terms (SAT.current_tbox ()) in
    Debug.add_terms_of "terms_from_dec_proc" terms;
    let gf = mk_gf F.vrai in
    Inst.add_terms env.inst terms gf

  let instantiate_ground_preds env acc sa =
    List.fold_left
      (fun acc a ->
        try (A.Map.find a env.ground_preds) :: acc
        with Not_found -> acc
      )acc sa
      [@ocaml.ppwarning "!!! Possibles issues du to replacement of atoms that are facts with TRUE by mk_lit (and simplify)"]


  let new_instances env sa acc =
    let inst, acc = inst_env_from_atoms env acc sa in
    let inst = terms_from_dec_proc {env with inst=inst} in
    mround {env with inst = inst} acc


  type pending = {
    seen_f : SF.t;
    activate : Types.atom option MFF.t;
    new_vars : Types.var list;
    unit : Types.atom list list;
    nunit : Types.atom list list;
    updated : bool;
  }

  let rec pre_assume (env, acc) gf =
    let {F.f=f} = gf in
    if debug_sat() then
      fprintf fmt "Entry of pre_assume: Given %a@.@." F.print f;
    if SF.mem f acc.seen_f then env, acc
    else
      let acc = {acc with seen_f = SF.add f acc.seen_f} in
      try
        let _, ff = MF.find f env.gamma in
        match ff with
        | None    ->
          env, acc
          [@ocaml.ppwarning "TODO: should be assert failure?"]

        | Some ff ->
          if SAT.exists_in_lazy_cnf ff then env, acc
          else
            env,
            {acc with
              activate = MFF.add ff None acc.activate;
              updated = true}
      with Not_found ->
        Debug.assume gf;
        match F.view f with
        | F.Lemma _ ->
          let ff = FF.vrai in
          let _, old_sf =
            try MFF.find ff env.conj with Not_found -> 0, SF.empty
          in
          let env =
            {env with
              gamma = MF.add f (env.nb_mrounds, None)  env.gamma;
              conj  = MFF.add ff (env.nb_mrounds, SF.add f old_sf) env.conj }
          in
          let env, deds = axiom_def env gf Ex.empty in
          (* This assert is not true assert (dec_lvl = 0); *)
          let acc = {acc with updated = true} in
          List.fold_left
            (fun accu (gf, _) -> pre_assume accu gf) (env, acc) deds

        | _ ->
          let ff, axs, new_vars =
            FF.simplify f (fun f -> MF.find f env.abstr_of_axs) acc.new_vars
          in
          let acc = {acc with new_vars = new_vars} in
          let cnf_is_in_cdcl = MFF.mem ff env.conj in
          let _, old_sf =
            try MFF.find ff env.conj with Not_found -> 0, SF.empty
          in
          let env =
            {env with
              gamma = MF.add f (env.nb_mrounds, Some ff) env.gamma;
              conj  = MFF.add ff (env.nb_mrounds, SF.add f old_sf) env.conj }
          in
          Debug.simplified_form f ff;
          let env, deds =
            List.fold_left register_abstraction (env, []) axs
          in
          if FF.equal ff FF.vrai then env, acc
          else
            if cnf_is_in_cdcl then
              (* this means that there exists another F.t that is
                 equivalent to f. These two formulas have the same ff *)
              if SAT.exists_in_lazy_cnf ff then env, acc
              else
                env,
                {acc with
                  activate = MFF.add ff None acc.activate;
                  updated = true}
            else
              let ff_abstr,new_proxies,proxies_mp, new_vars =
                FF.cnf_abstr ff env.proxies acc.new_vars
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
                  activate = MFF.add ff None acc.activate;
                  updated = true
                }
              in
              List.fold_left pre_assume (env, acc) deds

  let cdcl_assume env pending ~dec_lvl =
    let { seen_f; activate; new_vars; unit; nunit; updated } = pending in
    (*
    fprintf fmt "pending : %d distinct forms@." (SF.cardinal seen_f);
    fprintf fmt "pending : %d to activate@." (SFF.cardinal activate);
    fprintf fmt "pending : %d new vars@." (List.length new_vars);
    fprintf fmt "pending : %d unit cnf@." (List.length unit);
    fprintf fmt "pending : %d non-unit cnf@." (List.length nunit);
    fprintf fmt "pending : updated = %b@." updated;
    *)
    if SF.is_empty seen_f then begin
      assert (MFF.is_empty activate);
      assert (new_vars == []);
      assert (unit == []);
      assert (nunit == []);
      assert (not updated);
    end
    else
      try
        let f = F.vrai
          [@ocaml.ppwarning "TODO: should fix for unsat cores generation"]
        in
        SAT.assume unit nunit f new_vars env.proxies ~cnumber:0;
        SAT.update_lazy_cnf activate ~dec_lvl;
      with
      | Satml.Unsat (lc)  -> raise (IUnsat (env, make_explanation lc))
      | Satml.Sat -> assert false


  let assume_aux ~dec_lvl env l =
    let pending = {
      seen_f = SF.empty; activate = MFF.empty;
      new_vars = []; unit = []; nunit = []; updated = false
    }
    in
    (*fprintf fmt "@.assume aux: %d@." (List.length l);*)
    let env, pending = List.fold_left pre_assume (env, pending) l in
    cdcl_assume env pending ~dec_lvl;
    env, pending.updated

  let frugal_instantiation env ~dec_lvl =
    Debug.new_instances "frugal-inst" env;
    let sa = atoms_from_sat_branches env ~greedy_round:false ~frugal:true in
    let l = instantiate_ground_preds env [] sa in
    let l = expand_skolems env l sa in
    let l = new_instances env sa l in
    let env, updated = assume_aux ~dec_lvl env l in
    env, updated

  let normal_instantiation env ~dec_lvl =
    Debug.new_instances "normal-inst" env;
    let sa = atoms_from_sat_branches env ~greedy_round:false ~frugal:false in
    let l = instantiate_ground_preds env [] sa in
    let l = expand_skolems env l sa in
    let l = new_instances env sa l in
    let env, updated = assume_aux ~dec_lvl env l in
    env, updated


  let greedy_instantiation env ~dec_lvl =
    assert (dec_lvl == SAT.decision_level ());
    if greedy () then raise (I_dont_know env);

    Debug.new_instances "greedy-inst" env;
    let sa = atoms_from_sat_branches env ~greedy_round:true ~frugal:false in
    (* FLASH -> bugfix: SHOULD instantiate ground preds to add more
       terms into instantiation engine !  --> for the same reasons,
       also expand skolems *)
    let l = instantiate_ground_preds env [] sa in
    let l = expand_skolems env l sa in
    let l = new_instances env sa l in
    let env, updated = assume_aux ~dec_lvl env l in
    env, updated


  let rec unsat_rec env ~first_call : unit =
    try SAT.solve (); assert false
    with
      | Satml.Unsat lc -> raise (IUnsat (env, make_explanation lc))
      | Satml.Sat ->
        (*if first_call then SAT.cancel_until 0;*)
        let env = {env with nb_mrounds = env.nb_mrounds + 1}
          [@ocaml.ppwarning
              "TODO: first intantiation a la DfsSAT before searching ..."]
        in
        if Options.profiling() then Profiling.instantiation env.nb_mrounds;
        let dec_lvl = SAT.decision_level () in

        let env, updated = frugal_instantiation env ~dec_lvl in
        let env, updated =
          if updated then env, true
          else
            let env, updated = normal_instantiation env ~dec_lvl in
            if updated then env, true else greedy_instantiation env ~dec_lvl
        in
        if not updated then raise (I_dont_know env);
        unsat_rec env ~first_call:false

  (* copied from sat_solvers.ml *)
  let max_term_depth_in_sat env =
    let aux mx f = Pervasives.max mx (F.max_term_depth f) in
    let max_t = MF.fold (fun f _ mx -> aux mx f) env.gamma 0 in
    A.Map.fold (fun _ {F.f} mx -> aux mx f) env.ground_preds max_t

  let unsat env gf =
    Debug.unsat gf;
    (*fprintf fmt "FE.unsat@.";*)
    (* In dfs_sat goals' terms are added to env.inst *)
    let env =
      {env with inst =
	  Inst.add_terms env.inst (F.ground_terms_rec gf.F.f) gf} in
    try
      assert (SAT.decision_level () == 0);
      let env, updated = assume_aux ~dec_lvl:0 env [gf] in
      let max_t = max_term_depth_in_sat env in
      let env = {env with inst = Inst.register_max_term_depth env.inst max_t} in
      unsat_rec env ~first_call:true;
      assert false
    with IUnsat (env, dep) ->
      if replay_satml_dfs () then Replay.replay_with_dfs env;
      dep

  let assume env gf =
    assert (SAT.decision_level () == 0);
    try fst (assume_aux ~dec_lvl:0 env [gf])
    with IUnsat (env, dep) -> raise (Unsat dep)

  let retrieve_used_context {inst=inst} = Inst.retrieve_used_context inst




(* instrumentation of relevant exported functions for profiling *)
  let assume t ff =
    if not (Options.timers ()) then assume t ff
    else
      try
        Timers.exec_timer_start Timers.M_Sat Timers.F_assume;
        let t = assume t ff in
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

  let assume_th_elt env th_elt = SAT.assume_th_elt th_elt; env

end

let () = Sat_solver.set_current (module Main : Sat_solver_sig.S)
