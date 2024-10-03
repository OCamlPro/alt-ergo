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

let src = Logs.Src.create ~doc:"Sat" __MODULE__
module Log = (val Logs.src_log src : Logs.LOG)

module Make (Th : Theory.S) : Sat_solver_sig.S = struct
  module SAT = Satml.Make(Th)
  module Inst = Instances.Make(Th)
  module Ex = Explanation
  module E = Expr
  module ME = E.Map
  module SE = E.Set
  module Atom = Satml_types.Atom
  module FF = Satml_types.Flat_Formula

  let reset_refs () = Steps.reset_steps ()

  type guards = {
    mutable current_guard: E.t;
    stack_guard: E.t Stack.t;
  }

  type t = {
    satml : SAT.t;
    ff_hcons_env : FF.hcons_env;
    mutable nb_mrounds : int;
    mutable last_forced_normal : int;
    mutable last_forced_greedy : int;
    mutable gamma : (int * FF.t option) ME.t;
    mutable conj : (int * SE.t) FF.Map.t;
    mutable abstr_of_axs : (FF.t * Atom.atom) ME.t;
    mutable axs_of_abstr : (E.t * Atom.atom) ME.t;
    mutable proxies : FF.proxies;
    mutable inst : Inst.t;
    mutable skolems : E.gformula ME.t; (* key <-> f *)
    add_inst : E.t -> bool;
    guards : guards;
    mutable last_saved_model : Models.t Lazy.t option;
    mutable last_saved_objectives : Objective.Model.t option;
    mutable unknown_reason : Sat_solver_sig.unknown_reason option;
    (** The reason why satml raised [I_dont_know] if it does; [None] by
        default. *)

    mutable declare_top : Id.typed list;
    declare_tail : Id.typed list Stack.t;
    (** Stack of the declared symbols by the user. The field [declare_top]
        is the top of the stack and [declare_tail] is tail. In particular, this
        stack is never empty. *)
  }

  let empty_guards () = {
    current_guard = Expr.vrai;
    stack_guard = Stack.create ();
  }

  let init_guards () =
    let guards = empty_guards () in
    Stack.push Expr.vrai guards.stack_guard;
    guards

  let empty ?(selector=fun _ -> true) () =
    let ff_hcons_env = FF.empty_hcons_env () in
    { gamma = ME.empty;
      satml = SAT.create (FF.atom_hcons_env ff_hcons_env);
      ff_hcons_env ;
      nb_mrounds = 0;
      last_forced_normal = 0;
      last_forced_greedy = 0;
      conj = FF.Map.empty;
      abstr_of_axs = ME.empty;
      axs_of_abstr = ME.empty;
      proxies = FF.empty_proxies;
      inst = Inst.empty;
      skolems = ME.empty;
      guards = init_guards ();
      add_inst = selector;
      last_saved_model = None;
      last_saved_objectives = None;
      unknown_reason = None;
      declare_top = [];
      declare_tail = Stack.create ();
    }

  exception Sat
  exception Unsat of Explanation.t
  exception I_dont_know

  let i_dont_know env ur =
    env.unknown_reason <- Some ur;
    raise I_dont_know

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
    open Printer

    let pred_def f =
      if Options.get_debug_sat () then
        print_dbg
          ~module_name:"Satml_frontend" ~function_name:"pred_def"
          "I assume a predicate: %a" E.print f

    let unsat gf =
      if Options.get_debug_sat () then
        print_dbg
          ~module_name:"Satml_frontend" ~function_name:"unsat"
          "unsat of %a ?" E.print gf.E.ff

    let assume gf =
      let { E.ff = f; lem; from_terms = terms; _ } = gf in
      if Options.get_debug_sat () then begin
        match E.form_view f with
        | E.Unit _ -> ()

        | E.Clause _ ->
          print_dbg ~module_name:"Satml_frontend" ~function_name:"assume"
            "I assume a clause %a" E.print f

        | E.Lemma _ ->
          print_dbg ~module_name:"Satml_frontend" ~function_name:"assume"
            "I assume a [%d-atom] lemma: %a"
            (E.size f) E.print f

        | E.Literal a ->
          let n = match lem with
            | None -> ""
            | Some ff -> begin
                match E.form_view ff with
                | E.Lemma xx -> xx.E.name
                | E.Unit _ | E.Clause _ | E.Literal _ | E.Skolem _
                | E.Let _ | E.Iff _ | E.Xor _ -> ""
              end
          in
          print_dbg ~module_name:"Satml_frontend" ~function_name:"assume"
            "@[<v 0>I assume a literal (%s : %a) %a@,\
             ================================================@]"
            n E.print_list terms E.print a;

        | E.Skolem _ ->
          print_dbg ~module_name:"Satml_frontend" ~function_name:"assume"
            "I assume a skolem %a" E.print f

        | E.Let _ ->
          print_dbg ~module_name:"Satml_frontend" ~function_name:"assume"
            "I assume a let-In %a" E.print f

        | E.Iff _ ->
          print_dbg ~module_name:"Satml_frontend" ~function_name:"assume"
            "I assume an equivalence %a" E.print f

        | E.Xor _ ->
          print_dbg ~module_name:"Satml_frontend" ~function_name:"assume"
            "I assume a neg-equivalence/Xor %a" E.print f

      end

    let simplified_form f f' =
      if Options.(get_debug_sat () && get_verbose ()) then
        print_dbg
          ~module_name:"Satml_frontend" ~function_name:"simplified_form"
          "@[<v 2>Simplified form of: %a@,is: %a@]"
          E.print f
          FF.print f'

    (* unused --
       let cnf_form f unit non_unit =
       if get_debug_sat () && get_verbose () then begin
        print_dbg "[sat] CFF form of: %a" FF.print f;
        print_dbg "  is:";
        List.iter
          (List.iter (fun a ->
          print_dbg "UNIT: %a" Atom.pr_atom a))
          unit;
        List.iter
          (fun c ->
             print_dbg "CLAUSE: ";
             List.iter (fun a ->
             print_dbg "%a or " Atom.pr_atom a) c;
          )non_unit
       end
    *)

    let model fmt env =
      if Options.get_debug_sat () then
        let model = SAT.boolean_model env.satml in
        let print fmt a =
          Format.fprintf fmt " %f | %a@,"
            (Atom.weight a)
            Atom.pr_atom a
        in
        Format.fprintf fmt
          "@[<v 2>(2) satML's model:@,%a@]"
          (pp_list_no_space print) (List.rev model)

    let new_instances mode env =
      if Options.get_debug_sat () then begin
        print_dbg ~flushed:false
          ~module_name:"Satml_frontend" ~function_name:"new_instances"
          "@[<v 2>I GENERATE NEW INSTANCES (%s)#################@,\
           @[<v 2>(1) ground problem:@,"
          mode;
        FF.Map.iter (fun f (md, _) ->
            print_dbg ~flushed:false ~header:false
              "-> %d : %a@," md FF.print f) env.conj;
        print_dbg ~header:false "@]@,%a"
          model env;
      end

    (* unused --
       let generated_instances l =
       if get_verbose () && get_debug_sat () then begin
        print_dbg "[new_instances] %d generated" (List.length l);
        List.iter (fun { E.ff = f; origin_name; _ } ->
            print_dbg " instance(origin = %s): %a" origin_name E.print f;
          ) l
       end
    *)

    (* unused --
       let trivial_fact p inst =
       if get_verbose () && get_debug_sat () then begin
        if inst then
        print_dbg "already known instance: %a" E.print p
        else
        print_dbg "already known skolem: %a" E.print p
       end
    *)

    (* unused --
       let generated_skolems l =
       if get_verbose () && get_debug_sat () then begin
        print_dbg "[new_skolems] %d generated" (List.length l);
        List.iter (fun { E.ff = f; _ } ->
        print_dbg " skolem: %a" E.print f) l
       end
    *)

    let atoms_from_sat_branch f =
      if Options.(get_verbose () && get_debug_sat ()) then
        print_dbg
          ~module_name:"Satml_frontend" ~function_name:"atoms_from_sat_branch"
          "[extract_and_add_terms from] %a" FF.print f

    let add_terms_of src terms =
      if Options.(get_verbose () && get_debug_sat ()) then begin
        print_dbg ~flushed:false ~module_name:"Satml_frontend"
          ~function_name:"add_terms_of"
          "@[<v 2>[%s] add_terms_of:@," src;
        SE.iter (fun e ->
            print_dbg ~flushed:false ~header:false
              ">> %a@," E.print e) terms;
        print_dbg ~header:false "@]"
      end

    (* unused --
       let axiom_def f =
       if get_debug_sat () then
       print_dbg
       (asprintf "[sat] I assume an axiom: %a" E.print f)
    *)

    let internal_axiom_def f a at =
      if Options.get_debug_sat () then
        print_dbg
          ~module_name:"Satml_frontend" ~function_name:"internal_axiom_def"
          "I assume an internal axiom: %a <-> %a@,\
           at of a is %a"
          E.print a E.print f
          Atom.pr_atom at

    (* unused --
       let in_mk_theories_instances () =
       if Options.get_debug_fpa() > 0 || get_debug_sat() then
       print_dbg
       "[sat] entering mk_theories_instances:"
    *)

    (* unused --
       let out_mk_theories_instances normal_exit =
       if Options.get_debug_fpa() > 0 || get_debug_sat() then
        if normal_exit then
        print_dbg "[sat] normal exit of mk_theories_instances."
        else
        print_dbg "exit mk_theories_instances with Inconsistency."
    *)

    let print_f_conj fmt hyp =
      match hyp with
      | [] -> Format.fprintf fmt "True";
      | e::l ->
        Format.fprintf fmt "%a" E.print e;
        List.iter (fun f -> Format.fprintf fmt " /\\  %a" E.print f) l

    let print_theory_instance hyp gf =
      if Options.get_debug_fpa() > 1 || Options.get_debug_sat() then
        print_dbg
          ~module_name:"Satml_frontend" ~function_name:"theory_instance"
          "@[<v 2>%s >@,\
           hypotheses: %a@,\
           conclusion: %a@]"
          (E.name_of_lemma_opt gf.E.lem)
          print_f_conj hyp
          E.print gf.E.ff;

  end
  (*BISECT-IGNORE-END*)

  let make_explanation _ = Ex.empty
  (*
    if get_debug_sat () then
    fprintf fmt "make_explanation of %d clauses@." (List.length lc);
    List.fold_left
    (fun ex ({ST.form = f} as c) ->
    if get_debug_sat () then
    fprintf fmt "unsat_core: %a@." Atom.pr_clause c;
    Ex.union (Ex.singleton (Ex.Dep f)) ex
  )Ex.empty lc*)

  let selector env f orig =
    (Options.get_cdcl_tableaux () || not (ME.mem f env.gamma))
    && begin match E.form_view orig with
      | E.Lemma _ -> env.add_inst orig
      | E.Unit _ | E.Clause _ | E.Literal _ | E.Skolem _
      | E.Let _ | E.Iff _ | E.Xor _ -> true
    end

  (* <begin> copied from sat_solvers.ml *)

  let reduce_filters acc (hyp, gf, dep) =
    Debug.print_theory_instance hyp gf;
    let clause =
      List.fold_left
        (fun tmp f ->
           (* we cannot reduce like in DfsSAT *)
           E.mk_or (E.neg f) tmp false
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
    if Options.get_profiling() then Profiling.instances l2;
    let gd1, ngd1 =
      Inst.m_lemmas menv env.inst tbox (selector env) env.nb_mrounds
    in
    let l1 = List.rev_append (List.rev gd1) ngd1 in
    if Options.get_profiling() then Profiling.instances l1;
    let l = ((List.rev_append l2 l1) : (E.gformula * Explanation.t) list) in

    let th_insts = mk_theories_inst_rec env 10 in
    let l = List.rev_append th_insts l in
    List.fold_left
      (fun acc (gf, dep) ->
         match literals_of_ex dep with
         | []  ->
           (* Toplevel assertions from [axiom_def] have no literals *)
           gf :: acc
         | [{ Atom.lit; _ }] -> (
             (* Instantiations from [internal_axiom_def] are justified by a
                single syntaxic literal (from [axs_of_abstr]) *)
             match Shostak.Literal.view lit with
             | LTerm lit ->
               {gf with
                E.ff =
                  E.mk_or gf.E.ff (E.neg lit) false} :: acc
             | LSem _ -> assert false
           )
         | _   -> assert false
      )acc l


  let pred_def env f name dep _loc =
    (* dep currently not used. No unsat-cores in satML yet *)
    Debug.pred_def f;
    let guard = env.guards.current_guard in
    env.inst <- Inst.add_predicate env.inst ~guard ~name (mk_gf f) dep

  let axiom_def env gf ex =
    env.inst <- Inst.add_lemma env.inst gf ex

  let internal_axiom_def ax a at inst =
    Debug.internal_axiom_def ax a at;
    let gax = mk_gf ax in
    let ex = Ex.singleton (Ex.Literal at) in
    Inst.add_lemma inst gax ex

  let register_abstraction env new_abstr_vars (f, (af, at)) =
    if Options.(get_debug_sat () && get_verbose ()) then
      Printer.print_dbg
        ~module_name:"Satml_frontend" ~function_name:"register_abstraction"
        "abstraction of %a is %a" E.print f FF.print af;
    let lat =
      match Shostak.Literal.view @@ Atom.literal at with
      | LTerm at -> at
      | LSem _ ->
        (* Abstractions are always fresh expressions, so `at` is always a
           syntaxic literal *)
        assert false
    in
    let new_abstr_vars =
      if not (Atom.is_true at) then at :: new_abstr_vars else new_abstr_vars
    in
    assert (not (ME.mem f env.abstr_of_axs));
    assert (not (ME.mem lat env.axs_of_abstr));
    let () =
      if not (Atom.eq_atom at Atom.vrai_atom || Atom.eq_atom at Atom.faux_atom)
      then
        begin
          env.abstr_of_axs <- ME.add f (af, at) env.abstr_of_axs;
          env.axs_of_abstr <- ME.add lat (f, at) env.axs_of_abstr
        end
    in
    if Atom.level at = 0 then (* at is necessarily assigned if lvl = 0 *)
      if Atom.is_true at then
        let () = axiom_def env (mk_gf f) Ex.empty in
        new_abstr_vars
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
        | E.Let _ | E.Iff _ | E.Xor _ -> assert false
      in
      (*XXX TODO: internal skolems*)
      let f = E.mk_or lat ded false in
      let nlat = E.neg lat in
      (* semantics: nlat ==> f *)
      env.skolems <- ME.add nlat (mk_gf f) env.skolems;
      new_abstr_vars
    end

  let expand_skolems env acc sa inst_quantif =
    List.fold_left
      (fun acc a ->
         if Options.(get_debug_sat () && get_verbose ()) then
           Printer.print_dbg
             ~module_name:"Satml_frontend" ~function_name:"expand_skolems"
             "expand skolem of %a" E.print a;
         try
           if inst_quantif a then
             let { E.ff = f; _ } as gf = ME.find a env.skolems in
             if not (Options.get_cdcl_tableaux ()) && ME.mem f env.gamma then
               acc
             else
               gf :: acc
           else
             acc
         with Not_found -> acc
      ) acc sa

  let inst_env_from_atoms env acc sa inst_quantif =
    List.fold_left
      (fun (inst, acc) a ->
         let gf = mk_gf E.vrai in
         if Options.(get_debug_sat () && get_verbose ()) then
           Printer.print_dbg
             ~module_name:"Satml_frontend" ~function_name:"inst_env_from_atoms"
             "terms_of_atom %a" E.print a;
         let inst = Inst.add_terms inst (E.max_ground_terms_of_lit a) gf in
         (* ax <-> a, if ax exists in axs_of_abstr *)
         try
           let ax, at = ME.find a env.axs_of_abstr in
           if inst_quantif a then
             internal_axiom_def ax a at inst, acc
           else
             inst, acc
         with Not_found -> inst, acc
      ) (env.inst, acc) sa

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
        else
          Some [
            match Shostak.Literal.view @@ Atom.literal at with
            | LTerm at -> at
            | LSem _ ->
              (* Flat formulas only contain syntaxic literals. *)
              assert false
          ]

      | FF.AND l ->
        begin
          try
            let acc =
              List.fold_left (fun lz f ->
                  match atoms_from_sat_branch f with
                  | None -> raise Exit
                  | Some l -> List.rev_append l lz
                ) [] l
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
           | Some l -> List.fold_left (fun sa a -> SE.add a sa) sa l
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
      let add_elit a s =
        match Shostak.Literal.view @@ Atom.literal a with
        | LTerm a -> SE.add a s
        | LSem _ -> s
      in
      SA.fold add_elit sa SE.empty

  let atoms_from_lazy_greedy env =
    let aux accu ff =
      let sf =
        try FF.Map.find ff env.conj |> snd
        with Not_found ->
          if FF.equal ff FF.vrai then SE.empty
          else begin
            Printer.print_err
              "%a not found in env.conj" FF.print ff;
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
    let sa = match greedy_round, Options.get_cdcl_tableaux_inst () with
      | false, false -> atoms_from_sat_branches env
      | false, true  -> atoms_from_lazy_sat ~frugal env
      | true , false -> atoms_from_bmodel env
      | true,  true  -> atoms_from_lazy_greedy env
    in
    let inst_quantif =
      if Options.get_cdcl_tableaux_inst () then
        let frugal = atoms_from_lazy_sat ~frugal:true env in
        (fun a -> SE.mem a frugal)
      else
        (fun _ -> true)
    in
    SE.elements sa, inst_quantif
    [@ocaml.ppwarning "Issue for greedy: terms inside lemmas not extracted"]

  let terms_from_dec_proc env =
    let terms = Th.extract_ground_terms (SAT.current_tbox env.satml) in
    Debug.add_terms_of "terms_from_dec_proc" terms;
    let gf = mk_gf E.vrai in
    Inst.add_terms env.inst terms gf

  let instantiate_ground_preds env acc sa =
    List.fold_left
      (fun acc a ->
         match Inst.ground_pred_defn a env.inst with
         | Some (guard, res, _dep) ->
           (* To be correct in incremental mode, we'll generate the
              formula "guard -> (a -> res)" *)
           let tmp = E.mk_imp a res in
           let tmp = E.mk_imp guard tmp in
           (mk_gf tmp)  :: acc
         | None ->
           acc
      )acc sa
    [@ocaml.ppwarning "!!! Possibles issues du to replacement of atoms \
                       that are facts with TRUE by mk_lit (and simplify)"]


  let new_instances use_cs env sa inst_quantif acc =
    let inst, acc = inst_env_from_atoms env acc sa inst_quantif in
    let inst = terms_from_dec_proc {env with inst=inst} in
    mround use_cs {env with inst = inst} acc


  type pending = {
    seen_f : SE.t;
    activate : FF.Set.t;
    new_vars : Atom.var list;
    unit : Atom.atom list list;
    nunit : Atom.atom list list;
    new_abstr_vars : Atom.atom list;
    updated : bool;
  }

  let pre_assume env acc gf =
    let { E.ff = f; _ } = gf in
    if Options.(get_debug_sat () && get_verbose ()) then
      Printer.print_dbg
        ~module_name:"Satml_frontend" ~function_name:"pre_assume"
        "Entry of pre_assume: Given %a" E.print f;
    if SE.mem f acc.seen_f then acc
    else
      let acc = {acc with seen_f = SE.add f acc.seen_f} in
      try
        let _, ff = ME.find f env.gamma in
        match ff with
        | None ->
          acc
          [@ocaml.ppwarning "TODO: should be assert failure?"]
        | Some ff ->
          if SAT.exists_in_lazy_cnf env.satml ff then acc
          else
            {acc with
             activate = FF.Set.add ff acc.activate;
             updated = true}
      with Not_found ->
        Debug.assume gf;
        match E.form_view f with
        | E.Lemma _ ->
          let ff = FF.vrai in
          let _, old_sf =
            try FF.Map.find ff env.conj with Not_found -> 0, SE.empty
          in
          env.gamma <- ME.add f (env.nb_mrounds, None) env.gamma;
          env.conj <- FF.Map.add ff (env.nb_mrounds, SE.add f old_sf) env.conj;
          (* This assert is not true assert (dec_lvl = 0); *)
          axiom_def env gf Ex.empty;
          {acc with updated = true}

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
          env.gamma <- ME.add f (env.nb_mrounds, Some ff) env.gamma;
          env.conj <- FF.Map.add ff (env.nb_mrounds, SE.add f old_sf) env.conj;
          Debug.simplified_form f ff;
          let new_abstr_vars =
            List.fold_left (register_abstraction env) acc.new_abstr_vars axs
          in
          let acc = { acc with new_abstr_vars } in
          if FF.equal ff FF.vrai then acc
          else
          if cnf_is_in_cdcl then
            (* this means that there exists another E.t that is
               equivalent to f. These two formulas have the same ff *)
            if SAT.exists_in_lazy_cnf env.satml ff then acc
            else
              {acc with
               activate = FF.Set.add ff acc.activate;
               updated = true}
          else
            let ff_abstr,new_proxies,proxies_mp, new_vars =
              FF.cnf_abstr env.ff_hcons_env ff env.proxies acc.new_vars
            in
            env.proxies <- proxies_mp;
            let nunit =
              List.fold_left FF.expand_proxy_defn acc.nunit new_proxies
            in
            let acc =
              {acc with
               new_vars;
               nunit;
               unit = [ff_abstr] :: acc.unit;
               activate = FF.Set.add ff acc.activate;
               updated = true
              }
            in
            acc

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
      assert (FF.Set.is_empty activate);
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
        SAT.assume env.satml unit nunit f ~cnumber:0 activate ~dec_lvl;
      with
      | Satml.Unsat (lc) -> raise (IUnsat (env, make_explanation lc))
      | Satml.Sat -> assert false

  let assume_aux_bis ~dec_lvl env l : bool * Atom.atom list =
    let pending = {
      seen_f = SE.empty; activate = FF.Set.empty;
      new_vars = []; unit = []; nunit = []; updated = false;
      new_abstr_vars = [];
    }
    in
    (*fprintf fmt "@.assume aux: %d@." (List.length l);*)
    let pending = List.fold_left (pre_assume env) pending l in
    cdcl_assume env pending ~dec_lvl;
    pending.updated, pending.new_abstr_vars

  let rec assume_aux ~dec_lvl env l =
    let updated, new_abstr_vars = assume_aux_bis ~dec_lvl env l in
    let elit a =
      match Shostak.Literal.view @@ Atom.literal a with
      | LTerm a -> a
      | LSem _ ->
        (* This is only called on newly added skolems, which are always
           syntaxic literals *)
        assert false
    in
    let bot_abstr_vars = (* try to immediately expand newly added skolems *)
      List.fold_left (fun acc at ->
          let neg_at = Atom.neg at in
          if Atom.is_true neg_at then (elit neg_at) :: acc else acc
        )[] new_abstr_vars
    in
    match bot_abstr_vars with
    | [] -> updated
    | _ ->
      let res = expand_skolems env [] bot_abstr_vars (fun _ -> true) in
      if res == [] then updated
      else
        let updated' = assume_aux ~dec_lvl env res in
        updated || updated'


  let frugal_mconf () =
    let open Options in
    {Util.nb_triggers = get_nb_triggers ();
     no_ematching = get_no_ematching();
     triggers_var = get_triggers_var ();
     use_cs = false;
     backward = Util.Normal;
     greedy = false;
    }

  let normal_mconf () =
    let open Options in
    {Util.nb_triggers = Stdlib.max 2 (get_nb_triggers () * 2);
     no_ematching = get_no_ematching();
     triggers_var = get_triggers_var ();
     use_cs = false;
     backward = Util.Normal;
     greedy = false;
    }

  let greedy_mconf () =
    let open Options in
    {Util.nb_triggers = Stdlib.max 10 (get_nb_triggers () * 10);
     no_ematching = false;
     triggers_var = get_triggers_var ();
     use_cs = true;
     backward = Util.Normal;
     greedy = true;
    }

  let greedier_mconf () =
    let open Options in
    {Util.nb_triggers = Stdlib.max 10 (get_nb_triggers () * 10);
     no_ematching = false;
     triggers_var = true;
     use_cs = true;
     backward = Util.Normal;
     greedy = true;
    }

  let do_instantiation env sa inst_quantif mconf msg ~dec_lvl =
    Debug.new_instances msg env;
    let l = instantiate_ground_preds env [] sa in
    let l = expand_skolems env l sa inst_quantif in
    let l = new_instances mconf env sa inst_quantif l in
    assume_aux ~dec_lvl env l

  type instantiation_strat =
    | Auto
    | Force_normal
    | Force_greedy


  let instantiation env inst_strat dec_lvl =
    let nb_mrounds = env.nb_mrounds in
    match inst_strat with
    | Force_normal ->
      let mconf = frugal_mconf () in (* take frugal_mconf if normal is forced *)
      env.last_forced_normal <- nb_mrounds;
      let sa, inst_quantif =
        instantiation_context env ~greedy_round:false ~frugal:false in
      do_instantiation env sa inst_quantif mconf "normal-inst (forced)" ~dec_lvl

    | Force_greedy ->
      let mconf = normal_mconf () in (*take normal_mconf if greedy is forced*)
      env.last_forced_greedy <- nb_mrounds;
      let sa, inst_quantif =
        instantiation_context env ~greedy_round:true ~frugal:true in
      do_instantiation env sa inst_quantif mconf "greedy-inst (forced)" ~dec_lvl

    | Auto ->
      List.fold_left
        (fun updated (mconf, debug, greedy_round, frugal) ->
           if updated then updated
           (* TODO: stop here with an exception *)
           else
             let sa, inst_quantif =
               instantiation_context env ~greedy_round ~frugal in
             do_instantiation env sa inst_quantif mconf debug ~dec_lvl
        )
        false
        (match Options.get_instantiation_heuristic () with
         | INormal ->
           [ frugal_mconf (), "frugal-inst", false, true ;
             normal_mconf (), "normal-inst", false, false ]
         | IAuto ->
           [ frugal_mconf (), "frugal-inst", false, true ;
             normal_mconf (), "normal-inst", false, false;
             greedier_mconf (), "greedier-inst", true, false]
         | IGreedy ->
           [ greedy_mconf (), "greedy-inst", true , false;
             greedier_mconf (), "greedier-inst", true, false])

  let do_case_split env policy =
    match SAT.do_case_split env.satml policy with
    | C_none -> ()
    | C_bool _ -> assert false
    | C_theory expl -> raise (Ex.Inconsistent (expl, []))

  let may_update_last_saved_model env compute =
    let compute =
      if not (Options.get_first_interpretation ()) then compute
      else env.last_saved_model == None
    in
    if compute then begin
      try
        (* also performs case-split and pushes pending atoms to CS *)
        let declared_ids = env.declare_top in
        let model, objectives =
          SAT.compute_concrete_model ~declared_ids env.satml
        in
        env.last_saved_model <- Some model;
        env.last_saved_objectives <- Some objectives;
      with Ex.Inconsistent (_expl, _classes) as e ->
        raise e
    end

  let update_model_and_return_unknown env compute_model ~unknown_reason =
    may_update_last_saved_model env compute_model;
    Options.Time.unset_timeout ();
    i_dont_know env unknown_reason

  exception Give_up of (E.t * E.t * bool * bool) list

  (* Getting [unknown] after a query can mean two things:
     - The problem is [unsat] but we didn't manage to find a contradiction;
     - We produce a model of the formulas.

     In the latter case, we optimized our objective functions during the
     exploration of this branch of the SAT solver. It doesn't mean there is no
     other branch of the SAT solver in which all the formulas are satisfiable
     and the objective functions have bigger values in some models of this
     branch.

     For instance, consider the SMT-LIB problem:
       (declare-const x Int)
       (assert (or (<= x 2) (<= x 4)))
       (assert (or (<= y 3))
       (maximize x)
       (maximize y)
       (check-sat)
       (get-model)

     Assume that the solver explores the first branch (<= x 2) of the or gate:
       (or (<= x 2) (<= x 4)).

     Let's imagine it discovers that [0] is a model of the first formula. After
     optimization, it find that [2] is the best model for [x] and [3] is the
     best model for [y] it can got in this branch. Still we have to explore
     the second branch [(<= x 4)] to realize that [4] is actually the best
     model for [x].

     The following function ensures to explore adequate branches of the SAT
     solver in order to get the best model, if the problem is SAT.

     In our running example, after getting the model [2], the below function
     run again the SAT solver with the extra assert:
       (assert (or (> x 2) (and (= x 2) (> y 3)))

     If this run produces the answer [unsat], we know that [2] was the best
     model value for [x]. Otherwise, we got a better value for [x]. *)

  type ty_op =
    { lt : E.t -> E.t -> E.t
    ; le : E.t -> E.t -> E.t }

  let real_op = { lt = Expr.Reals.(<) ; le = Expr.Reals.(<=) }

  let int_op = { lt = Expr.Ints.(<) ; le = Expr.Reals.(<=) }

  let bitv_unsigned_op = { lt = Expr.BV.bvult ; le = Expr.BV.bvule }

  let mk_le { le ; _ } = le

  let mk_lt { lt ; _ } = lt

  let mk_ge { le ; _ } x y = le y x

  let mk_gt { lt ; _ } x y = lt y x

  let op ty is_max is_le =
    let ty_op =
      match ty with
      | Ty.Treal -> real_op
      | Tint -> int_op
      | Tbitv _ -> bitv_unsigned_op
      | _ -> Fmt.invalid_arg "cannot optimize for type: %a" Ty.print ty
    in
    if is_max then begin
      if is_le then mk_le ty_op
      else mk_lt ty_op
    end
    else begin
      if is_le then mk_ge ty_op
      else mk_gt ty_op
    end

  (* This function is called after receiving an `I_dont_know` exception from
     unsat_rec. It may re-raise this exception. *)
  let analyze_unknown_for_objectives env unsat_rec_prem : unit =
    let objs =
      match env.last_saved_objectives with
      | Some objs -> objs
      | None -> raise I_dont_know
    in
    let acc =
      try
        Objective.Model.fold (fun { e; is_max; _ } value acc ->
            match (value : Objective.Value.t) with
            | Pinfinity | Minfinity ->
              raise (Give_up acc)
            | Value v ->
              (e, v, is_max, true) :: acc
            | Limit (_, v) ->
              raise (Give_up ((e, v, is_max, false) :: acc))
            | Unknown ->
              assert false
          ) objs []
      with Give_up acc -> acc
    in
    begin match acc with
      | [] ->
        (* The answer for the first objective is infinity. We stop here as
           we cannot go beyond infinity and the next objectives with lower
           priority cannot be optimized in presence of infinity values. *)
        raise I_dont_know;
      | (e, tv, is_max, is_le) :: l ->
        let neg =
          List.fold_left
            (fun acc (e, tv, is_max, is_le) ->
               let eq = E.mk_eq e tv ~iff: false in
               let acc = E.Core.and_ acc eq in
               E.Core.(or_ acc (not ((op (E.type_info e) is_max is_le) e tv)))
            ) (E.Core.not ((op (E.type_info e) is_max is_le) e tv)) l
        in
        if Options.get_debug_optimize () then
          Printer.print_dbg
            "The objective function %a has an optimum. We should continue \
             to explore other branches to try to find a better optimum than \
             %a." Expr.print e Expr.print tv;
        let l = [mk_gf neg] in
        (* TODO: Can we add the clause without 'cancel_until 0' ? *)
        SAT.cancel_until env.satml 0;
        if Options.get_debug_optimize () then
          Printer.print_dbg
            "We assert the formula %a to explore another branch."
            E.print neg;
        let updated = assume_aux ~dec_lvl:0 env l in
        if not updated then begin
          Printer.print_dbg
            "env not updated after injection of neg! termination \
             issue.@.@.";
          assert false
        end;
        Options.Time.unset_timeout ();
        Options.Time.set_timeout (Options.get_timelimit ());
        unsat_rec_prem env ~first_call:false
    end

  let rec unsat_rec env ~first_call:_ : unit =
    try SAT.solve env.satml; assert false
    with
    | Satml.Unsat lc -> raise (IUnsat (env, make_explanation lc))
    | Util.Timeout -> i_dont_know env (Timeout ProofSearch)
    | Util.Step_limit_reached n -> i_dont_know env (Step_limit n)
    | Satml.Sat ->
      try
        do_case_split env Util.BeforeMatching;
        may_update_last_saved_model env (Options.get_every_interpretation ());
        let () =
          env.nb_mrounds <- env.nb_mrounds + 1
                            [@ocaml.ppwarning
                              "TODO: first intantiation a la DfsSAT before \
                               searching ..."]
        in
        if Options.get_profiling() then Profiling.instantiation env.nb_mrounds;
        let strat =
          if env.nb_mrounds - env.last_forced_greedy > 1000 then Force_greedy
          else
          if env.nb_mrounds - env.last_forced_normal > 50 then Force_normal
          else Auto
        in
        (*let strat = Auto in*)
        let dec_lvl = SAT.decision_level env.satml in
        let updated = instantiation env strat dec_lvl in
        do_case_split env Util.AfterMatching;
        let updated =
          if not updated && strat != Auto then instantiation env Auto dec_lvl
          else updated
        in
        let dec_lvl' = SAT.decision_level env.satml in
        let () =
          if strat == Auto && dec_lvl' = dec_lvl then
            (* increase chances of forcing Normal each time Auto
               instantiation doesn't allow to backjump *)
            env.last_forced_normal <- env.last_forced_normal - 1
        in
        if not updated then
          update_model_and_return_unknown
            env (Options.get_last_interpretation ())
            ~unknown_reason:Incomplete; (* may becomes ModelGen *)
        unsat_rec env ~first_call:false

      with
      | Util.Timeout -> i_dont_know env (Timeout ProofSearch)
      | Util.Step_limit_reached n -> i_dont_know env (Step_limit n)
      | Satml.Unsat lc -> raise (IUnsat (env, make_explanation lc))
      | Ex.Inconsistent (expl, _cls) -> (*may be raised during matching or CS*)
        begin
          try
            SAT.conflict_analyze_and_fix env.satml (Satml.C_theory expl);
            unsat_rec env ~first_call:false
          with
          | Satml.Unsat lc -> raise (IUnsat (env, make_explanation lc))
          | Util.Timeout -> i_dont_know env (Timeout ProofSearch)
          | Util.Step_limit_reached n -> i_dont_know env (Step_limit n)
        end

  let rec unsat_rec_prem env ~first_call : unit =
    try
      unsat_rec env ~first_call
    with
    | I_dont_know ->
      begin
        try analyze_unknown_for_objectives env unsat_rec_prem
        with
        | IUnsat (env, _) ->
          assert (Option.is_some env.last_saved_objectives);
          (* objectives is a ref, it's necessiraly updated as a
             side-effect to best value *)
          raise I_dont_know
      end
    | IUnsat (env, _) as e ->
      if Option.is_none env.last_saved_objectives then raise e;
      (* TODO: put the correct objectives *)
      raise I_dont_know

  (* copied from sat_solvers.ml *)
  let max_term_depth_in_sat env =
    let aux mx f = Stdlib.max mx (E.depth f) in
    ME.fold (fun f _ mx -> aux mx f) env.gamma 0


  let checks_implemented_features () =
    let fails msg =
      let msg =
        Format.sprintf
          "%S is not implemented in CDCL solver ! \
           Please use the old Tableaux-like SAT solver instead."
          msg
      in
      Errors.run_error (Errors.Unsupported_feature msg)
    in
    let open Options in
    if get_save_used_context () then fails "save_used_context";
    if get_unsat_core () then fails "unsat_core"

  let create_guard env =
    let expr_guard = E.fresh_name Ty.Tbool in
    let ff, axs, new_vars =
      FF.simplify env.ff_hcons_env expr_guard
        (fun f -> ME.find f env.abstr_of_axs) []
    in
    assert (axs == []);
    match FF.view ff, new_vars with
    | FF.UNIT atom_guard, [v] ->
      assert (Atom.eq_atom atom_guard v.pa);
      let nbv = FF.nb_made_vars env.ff_hcons_env in
      (* Need to use new_vars function to add the new_var corresponding to
         the atom atom_guard in the satml env *)
      let u, nu = SAT.new_vars env.satml ~nbv new_vars [] [] in
      assert (u == [] && nu == []);
      expr_guard, atom_guard
    | _ -> assert false

  let declare env id =
    env.declare_top <- id :: env.declare_top

  let push env to_push =
    Util.loop ~f:(fun _n () () ->
        try
          let expr_guard, atom_guard = create_guard env in
          SAT.push env.satml atom_guard;
          Stack.push expr_guard env.guards.stack_guard;
          Steps.push_steps ();
          env.guards.current_guard <- expr_guard;
          Stack.push env.declare_top env.declare_tail;
        with
        | Util.Step_limit_reached _ ->
          (* This function should be called without step limit
             (see Steps.apply_without_step_limit) *)
          assert false
      )
      ~max:to_push
      ~elt:()
      ~init:()

  let pop env to_pop =
    Util.loop
      ~f:(fun _n () () ->
          SAT.pop env.satml;
          let guard_to_neg = Stack.pop env.guards.stack_guard in
          let inst = Inst.pop ~guard:guard_to_neg env.inst in
          assert (not (Stack.is_empty env.guards.stack_guard));
          let b = Stack.top env.guards.stack_guard in
          Steps.pop_steps ();
          env.last_saved_model <- None;
          env.last_saved_objectives <- None;
          env.inst <- inst;
          env.guards.current_guard <- b;
          let declare_top =
            try
              Stack.pop env.declare_tail
            with Stack.Empty ->
              Errors.error (Run_error Stack_underflow)
          in
          env.declare_top <- declare_top;
        )
      ~max:to_pop
      ~elt:()
      ~init:()

  let add_guard env gf =
    let current_guard = env.guards.current_guard in
    {gf with E.ff = E.mk_imp current_guard gf.E.ff}

  let unsat env gf =
    checks_implemented_features ();
    let gf = add_guard env gf in
    Debug.unsat gf;
    (*fprintf fmt "FF.unsat@.";*)
    (* In dfs_sat goals' terms are added to env.inst *)
    env.inst <-
      Inst.add_terms env.inst
        (E.max_ground_terms_rec_of_form gf.E.ff) gf;
    try
      assert (SAT.decision_level env.satml == 0);
      let _updated = assume_aux ~dec_lvl:0 env [gf] in
      let max_t = max_term_depth_in_sat env in
      env.inst <- Inst.register_max_term_depth env.inst max_t;
      unsat_rec_prem env ~first_call:true;
      assert false
    with
    | IUnsat (_env, dep) ->
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
    try ignore (assume_aux ~dec_lvl:0 env [add_guard env gf])
    with | IUnsat (_env, dep) -> raise (Unsat dep)
         | Util.Timeout ->
           (* don't attempt to compute a model if timeout before
              calling unsat function *)
           i_dont_know env (Timeout Assume)
         | Util.Step_limit_reached n ->
           (* When reaching the step limit on an assume, we do not want to
              answer 'unknown' right away. *)
           env.unknown_reason <- Some (Step_limit n)

  (* instrumentation of relevant exported functions for profiling *)
  let assume t ff dep =
    Timers.with_timer Timers.M_Sat Timers.F_assume @@ fun () ->
    assume t ff dep

  let unsat t ff =
    Timers.with_timer Timers.M_Sat Timers.F_unsat @@ fun () ->
    unsat t ff

  let assume_th_elt env th_elt dep =
    SAT.assume_th_elt env.satml th_elt dep

  let optimize env fn = SAT.optimize env.satml fn

  let get_model env =
    Option.map Lazy.force env.last_saved_model

  let get_unknown_reason env = env.unknown_reason

  let get_value env t =
    match E.type_info t with
    | Ty.Tbool ->
      begin
        let bmodel = SAT.boolean_model env.satml in
        Compat.List.find_map
          (fun Atom.{lit; neg = {lit=neglit; _}; _} ->
             let tlit = Shostak.Literal.make (LTerm t) in
             if Shostak.Literal.equal tlit lit then
               Some E.vrai
             else if Shostak.Literal.equal tlit neglit then
               Some E.faux
             else
               None
          )
          bmodel
      end
    | _ -> None

  let get_objectives env = env.last_saved_objectives

  let supports_optimization = true

  let reinit_ctx () =
    Steps.reinit_steps ();
    Th.reinit_cpt ();
    Id.Namespace.reinit ();
    Symbols.clear_labels ();
    Var.reinit_cnt ();
    Objective.Function.reinit_cnt ();
    Satml_types.Flat_Formula.reinit_cpt ();
    Ty.reinit_decls ();
    IntervalCalculus.reinit_cache ();
    Inst.reinit_em_cache ();
    Expr.reinit_cache ();
    Hstring.reinit_cache ();
    Shostak.Combine.reinit_cache ();
    Uf.reinit_cache ()

  let () =
    Steps.save_steps ();
    Var.save_cnt ();
    Expr.save_cache ();
    Hstring.save_cache ();
    Shostak.Combine.save_cache ();
    Uf.save_cache ()

end

(*
(*+ no dynamic loading of SAT solvers anymore +*)
let () = Sat_solver.set_current (module Main : Sat_solver_sig.S)
*)
