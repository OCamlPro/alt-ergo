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
module Ex = Explanation
module E = Expr
module A = Xliteral
module SE = Expr.Set

module Sy = Symbols

module type S = sig

  type t
  type r = Shostak.Combine.r

  val empty : t

  val empty_facts : unit -> r Sig_rel.facts

  val add_fact : r Sig_rel.facts -> r Sig_rel.fact -> unit

  val add_term :
    t ->
    r Sig_rel.facts -> (* acc *)
    Expr.t ->
    Explanation.t ->
    t * r Sig_rel.facts

  val add :
    t ->
    r Sig_rel.facts -> (* acc *)
    E.t ->
    Explanation.t -> t * r Sig_rel.facts

  val assume_literals :
    t ->
    (r Sig_rel.literal * Explanation.t * Th_util.lit_origin) list ->
    r Sig_rel.facts ->
    t * (r Sig_rel.literal * Explanation.t * Th_util.lit_origin) list

  val case_split : t -> for_model:bool -> Th_util.case_split list * t
  val optimizing_objective :
    t -> Objective.Function.t -> Th_util.optimized_split option

  val query :  t -> E.t -> Th_util.answer
  val new_terms : t -> Expr.Set.t
  val class_of : t -> Expr.t -> Expr.Set.t
  val are_equal : t -> Expr.t -> Expr.t -> init_terms:bool -> Th_util.answer
  val are_distinct : t -> Expr.t -> Expr.t -> Th_util.answer
  val cl_extract : t -> Expr.Set.t list
  val term_repr : t -> Expr.t -> init_term:bool -> Expr.t

  val get_union_find : t -> Uf.t

  val assume_th_elt : t -> Expr.th_elt -> Explanation.t -> t
  val theories_instances :
    do_syntactic_matching:bool ->
    Matching_types.info Expr.Map.t * Expr.t list Expr.Map.t Symbols.Map.t ->
    t -> (Expr.t -> Expr.t -> bool) -> t * Sig_rel.instances

  val extract_concrete_model :
    prop_model:Expr.Set.t ->
    declared_names:Symbols.typed_name list ->
    t -> Models.t

end

module Main : S = struct

  module SetA = Use.SA
  module Rel = Relation
  module Q = Queue
  module LR = Uf.LX

  type t = {
    use : Use.t;
    uf : Uf.t ;
    relation : Rel.t
  }

  type r = Shostak.Combine.r

  let empty =
    let uf = Uf.empty in
    let relation, domains = Rel.empty uf in
    let uf = Uf.set_domains uf domains in
    {
      use = Use.empty;
      uf;
      relation;
    }

  let empty_facts () =
    Sig_rel.{ equas   = Queue.create ();
              ineqs   = Queue.create ();
              diseqs  = Queue.create ();
              touched = Util.MI.empty }

  let add_fact (facts: r Sig_rel.facts) ((lit, _, _) as e) =
    match (lit: r Sig_rel.literal) with
    | LSem Xliteral.Pred _ | LSem Xliteral.Eq _ ->
      Queue.push e facts.equas
    | LSem Xliteral.Distinct _ -> Queue.push e facts.diseqs
    | LSem Xliteral.Builtin _  -> Queue.push e facts.ineqs
    | LTerm a ->
      match E.lit_view a with
      | E.Pred _ | E.Eq _ | E.Eql _ -> Queue.push e facts.equas
      | E.Distinct _ -> Queue.push e facts.diseqs
      | E.Builtin _  -> Queue.push e facts.ineqs

  (*BISECT-IGNORE-BEGIN*)
  module Debug = struct
    open Printer

    let facts (f: r Sig_rel.facts) msg =
      let aux fmt q =
        Q.iter
          (fun (lit,_,_) ->
             match (lit: r Sig_rel.literal) with
             | LSem sa ->
               Format.fprintf fmt "  > LSem  %a@." LR.print (LR.make sa)
             | LTerm a ->
               Format.fprintf fmt "  > LTerm %a@."E.print a
          )q
      in
      let aux2 fmt mp =
        Util.MI.iter
          (fun _ x -> Format.fprintf fmt "%a |-> ... (See Uf)@." X.print x) mp
      in
      if Options.get_debug_cc () then
        print_dbg
          ~module_name:"Ccx" ~function_name:"facts"
          "@[<v 0>I am in %s with the following facts@ \
           ---- Begin Facts -----------------------------------@ \
           Equalities:@ %a@ \
           Disequalities:@ %a@ \
           Inequalities:@ %a@ \
           Touched:@ %a@ \
           ---- End   Facts -----------------------------------@]"
          msg aux f.equas aux f.diseqs aux f.ineqs aux2 f.touched

    let cc r1 r2 =
      if Options.get_debug_cc () then
        print_dbg
          ~module_name:"Ccx" ~function_name:"cc"
          "congruence closure : %a = %a"
          X.print r1 X.print r2

    let make_cst t ctx =
      if ctx != [] then
        let c = ref 0 in
        let print fmt a =
          incr c;
          Format.fprintf fmt " %d) %a@ " !c E.print a
        in
        if Options.get_debug_cc () then
          print_dbg
            ~module_name:"Ccx" ~function_name:"make_ctx"
            "constraints of make(%a)@ %a"
            Expr.print t (pp_list_no_space print) ctx

    let rel_add_cst t ctx =
      if ctx != [] then
        let c = ref 0 in
        let print fmt (a, _ex) =
          incr c;
          Format.fprintf fmt " %d) %a@ " !c (A.print_view X.print) a
        in
        if Options.get_debug_cc () then
          print_dbg
            ~module_name:"Ccx" ~function_name:"rel_add_cst"
            "constraints of Rel.add(%a)@ %a"
            Expr.print t (pp_list_no_space print) ctx

    let add_to_use t =
      if Options.get_debug_cc () then
        print_dbg
          ~module_name:"Ccx" ~function_name:"add_to_use"
          "%a" E.print t

    (* unused --
       let lrepr fmt =
       List.iter (fprintf fmt) "%a " X.print)

       let leaves t lvs =
       print_dbg
        (asprintf "[cc] leaves of %a" E.print t); lrepr (get_fmt_dbg ()) lvs
    *)

    let contra_congruence a ex =
      if Options.get_debug_cc () then
        print_dbg
          ~module_name:"Ccx" ~function_name:"contra_congruence"
          "find that %a %a by contra-congruence"
          E.print a Ex.print ex

    let assume_literal sa =
      if Options.get_debug_cc () then
        print_dbg
          ~module_name:"Ccx" ~function_name:"assume_literal"
          "assume literal : %a" LR.print (LR.make sa)

    let congruent a ex =
      if Options.get_debug_cc () then
        print_dbg
          ~module_name:"Ccx" ~function_name:"congruent"
          "new fact by congruence : %a ex[%a]"
          E.print a Ex.print ex

    let cc_result p v touched =
      let print fmt (x,y,_) =
        Format.fprintf fmt "  > %a ~~ becomes ~> %a" X.print x X.print y
      in
      if Options.get_debug_cc () then
        print_dbg
          ~module_name:"Ccx" ~function_name:"cc_result"
          "the binding %a -> %a touched:@,%a"
          X.print p X.print v
          (pp_list_no_space print) touched

  end
  (*BISECT-IGNORE-END*)

  let one, _ = X.make (Expr.mk_term (Sy.name ~ns:Internal "@bottom") [] Ty.Tint)

  let concat_leaves uf l =
    let concat_rec acc t =
      match  X.leaves (fst (Uf.find uf t)) , acc with
        [] , _ -> one::acc
      | res, [] -> res
      | res , _ -> List.rev_append res acc
    in
    match List.fold_left concat_rec [] l with
      [] -> [one]
    | res -> res

  let explain_equality env ex t1 t2 =
    if E.equal t1 t2 then ex
    else match Uf.are_equal env.uf t1 t2 ~added_terms:true with
      | Some (dep, _) -> Ex.union ex dep
      | None -> raise Exit

  let equal_only_by_congruence env (facts: r Sig_rel.facts) t1 t2 =
    if not (E.equal t1 t2) then
      let { E.f = f1; xs = xs1; ty = ty1; _ } = E.term_view t1 in
      let { E.f = f2; xs = xs2; ty = ty2; _ } = E.term_view t2 in
      if Symbols.equal f1 f2 && Ty.equal ty1 ty2 then
        try
          let ex = List.fold_left2 (explain_equality env) Ex.empty xs1 xs2 in
          let a = E.mk_eq ~iff:false t1 t2 in
          Debug.congruent a ex;
          Q.push (Literal.LTerm a, ex, Th_util.Other) facts.equas
        with Exit -> ()

  let congruents env (facts: r Sig_rel.facts) t1 s =
    match E.term_view t1 with
    | { E.xs = []; _ } -> ()
    | { E.f; _ } when X.fully_interpreted f -> ()
    |  _ -> SE.iter (equal_only_by_congruence env facts t1) s

  let fold_find_with_explanation find ex l =
    List.fold_left
      (fun (lr, ex) t ->
         let r, ex_r = find t in r::lr, Ex.union ex_r ex)
      ([], ex) l

  let view find va ex_a =
    match va with
    | E.Pred (t1, b) ->
      let r1, ex1 = find t1 in
      let ex = Ex.union ex1 ex_a in
      LR.mkv_pred r1 b, ex
    | E.Eq (t1, t2) ->
      let r1, ex1 = find t1 in
      let r2, ex2 = find t2 in
      let ex = Ex.union (Ex.union ex1 ex2) ex_a in
      LR.mkv_eq r1 r2, ex
    | E.Eql lt ->
      let lr, ex = fold_find_with_explanation find ex_a lt in
      LR.mkv_distinct true (* not distinct*) (List.rev lr), ex
    | E.Distinct lt ->
      let lr, ex = fold_find_with_explanation find ex_a lt in
      LR.mkv_distinct false (*not neg*) (List.rev lr), ex
    | E.Builtin(b, s, l) ->
      let lr, ex  = fold_find_with_explanation find ex_a l in
      LR.mkv_builtin b s (List.rev lr), ex

  let view_r find va ex_a =
    match va with
    | Xliteral.Pred (t1, b) ->
      let r1, ex1 = find t1 in
      let ex = Ex.union ex1 ex_a in
      LR.mkv_pred r1 b, ex
    | Xliteral.Eq (t1, t2) ->
      let r1, ex1 = find t1 in
      let r2, ex2 = find t2 in
      let ex = Ex.union (Ex.union ex1 ex2) ex_a in
      LR.mkv_eq r1 r2, ex
    | Xliteral.Distinct (b, lt) ->
      let lr, ex = fold_find_with_explanation find ex_a lt in
      LR.mkv_distinct b (List.rev lr), ex
    | Xliteral.Builtin(b, s, l) ->
      let lr, ex  = fold_find_with_explanation find ex_a l in
      LR.mkv_builtin b s (List.rev lr), ex

  let term_canonical_view env a ex_a =
    view (Uf.find env.uf) (E.lit_view a) ex_a

  let canonical_view env a ex_a = view_r (Uf.find_r env.uf) a ex_a

  (* Begin: new implementation of add, add_term, assume_literals and all that *)

  let new_facts_by_contra_congruence env (facts: r Sig_rel.facts) r bol =
    match X.term_extract r with
    | None, _ -> ()
    | Some _, false -> () (* not an original term *)
    | Some t1, true ->  (* original term *)
      match E.term_view t1 with
      | { E.f = f1; xs = [x]; _ } ->
        let ty_x = Expr.type_info x in
        E.Set.iter
          (fun t2 ->
             match E.term_view t2 with
             | { E.f = f2 ; xs = [y]; _ } when Sy.equal f1 f2 ->
               let ty_y = Expr.type_info y in
               if Ty.equal ty_x ty_y then
                 begin match Uf.are_distinct env.uf t1 t2 with
                   | Some (ex_r, _) ->
                     let a = E.mk_distinct ~iff:false [x; y] in
                     Debug.contra_congruence a ex_r;
                     Q.push (Literal.LTerm a, ex_r, Th_util.Other) facts.diseqs
                   | None -> assert false
                 end
             | _ -> ()
          ) (Uf.class_of env.uf bol)
      | _ -> ()

  let clean_use =
    List.fold_left
      (fun env a ->
         match E.lit_view a with
         | E.Distinct lt
         | E.Builtin (_, _, lt) ->
           let lvs = concat_leaves env.uf lt in
           List.fold_left
             (fun env rx ->
                let st, sa = Use.find rx env.use in
                (* SetA does not use ex, so Ex.empty is OK for removing *)
                let sa = SetA.remove (a, Ex.empty) sa in
                { env with use = Use.add rx (st,sa) env.use }
             ) env lvs
         | _ -> assert false
      )

  let contra_congruence env facts r =
    Options.exec_thread_yield ();
    if X.equal (fst (Uf.find_r env.uf r)) X.top then
      new_facts_by_contra_congruence env facts r E.faux
    else if X.equal (fst (Uf.find_r env.uf r)) X.bot then
      new_facts_by_contra_congruence env facts r E.vrai

  let congruence_closure env (facts: r Sig_rel.facts) r1 r2 ex =
    Options.exec_thread_yield ();
    Debug.cc r1 r2;
    let uf, res = Uf.union env.uf r1 r2 ex in
    List.fold_left
      (fun env (p, touched, v) ->
         Options.exec_thread_yield ();
         Debug.cc_result p v touched;
         assert (X.is_a_leaf p);
         (* we look for use(p) *)
         let p_t, p_a = Use.find p env.use in

         (* we compute terms and atoms to consider for congruence *)
         let repr_touched = List.map (fun (x, y, _) ->
             facts.touched <-
               Util.MI.add (X.hash x) x facts.touched;
             y
           ) touched
         in
         let st_others, sa_others = Use.congr_close_up env.use p repr_touched in

         (* we update use *)
         let nuse = Use.up_close_up env.use p v in
         let nuse =
           List.fold_left
             (fun nuse (_, rr, _) ->
                match X.leaves rr with
                | _ :: _ -> nuse
                | []     -> Use.up_close_up nuse p one
             )nuse touched
         in
         Use.print nuse;

         (* we check the congruence of the terms. *)
         let env =  {env with use=nuse} in
         SE.iter (fun t -> congruents env facts t st_others) p_t;

         (*CC of preds ?*)
         SetA.iter (fun (a, ex) ->
             add_fact facts (LTerm a, ex, Th_util.Other)) p_a;

         (*touched preds ?*)
         SetA.iter (fun (a, ex) ->
             add_fact facts (LTerm a, ex, Th_util.Other))
           sa_others;

         env
      ) {env with uf=uf}  res

  module HLR =
    Hashtbl.Make (struct
      type t = LR.t * E.t option
      let equal (x, y) (x', y') =
        LR.equal x x' &&
        match y, y' with
        | None, None      ->  true
        | Some _, None    ->  false
        | None, Some _    -> false
        | Some a, Some a' -> E.equal a a'

      let hash (x, y) =
        match y with
        | None -> Hashtbl.hash (LR.hash x, 0)
        | Some e -> Hashtbl.hash (LR.hash x, E.hash e)
    end)

  let make_unique sa =
    match sa with
    | [] | [ _ ] -> sa
    | _ ->
      let table = HLR.create 17 in
      List.iter
        (fun ((ra, aopt ,_ , _) as e) ->
           (* Make sure to prefer equalities of [Subst] origin because they are
              used for partial computations (see {!Rel_utils}). In general, we
              want to make sure that the relations see all the equalities from
              representative changes in the union-find. *)
           let lra = LR.make ra in
           match HLR.find table (lra, aopt) with
           | (_, _, _, Th_util.Subst) -> ()
           | _ | exception Not_found -> HLR.replace table (lra, aopt) e
        ) sa;
      HLR.fold (fun _ e acc -> e::acc) table []

  let replay_atom env sa =
    Options.exec_thread_yield ();
    let sa = make_unique sa in
    let relation, domains, result = Rel.assume env.relation env.uf sa in
    let env = { env with uf = Uf.set_domains env.uf domains } in
    let env = { env with relation = relation } in
    let env = clean_use env result.remove in
    env, result.assume

  let rec add_term env facts t ex =
    Options.exec_thread_yield ();
    (* nothing to do if the term already exists *)
    if Uf.mem env.uf t then env
    else begin
      Options.tool_req 3 "TR-CCX-AddTerm";
      Debug.add_to_use t;

      (* we add t's arguments in env *)
      let { E.xs; _ } = E.term_view t in
      let env = List.fold_left (fun env t -> add_term env facts t ex) env xs in
      (* we update uf and use *)
      let nuf, ctx  = Uf.add env.uf t in
      Debug.make_cst t ctx;
      List.iter (fun a -> add_fact facts (LTerm a, ex, Th_util.Other)) ctx;
      (*or Ex.empty ?*)

      let rt, _ = Uf.find nuf t in
      let lvs = concat_leaves nuf xs in
      let nuse = Use.up_add env.use t rt lvs in

      (* If finitetest is used we add the term to the relation *)
      let rel, doms, eqs = Rel.add env.relation nuf rt t in
      let nuf = Uf.set_domains nuf doms in
      Debug.rel_add_cst t eqs;
      (* We add terms made from relations as fact *)
      List.iter (fun (a,ex) -> add_fact facts (LSem a, ex, Th_util.Other)) eqs;
      Use.print nuse;

      (* we compute terms to consider for congruence *)
      (* we do this only for non-atomic terms with uninterpreted
         head-symbol *)
      let st_uset = Use.congr_add nuse lvs in

      (* we check the congruence of each term *)
      let env = {uf = nuf; use = nuse; relation = rel} in
      congruents env facts t st_uset;
      env
    end

  let add env facts a ex =
    match E.lit_view a with
    | E.Pred (t1, _) ->
      add_term env facts t1 ex
    | E.Eq (t1, t2) ->
      let env = add_term env facts t1 ex in
      add_term env facts t2 ex
    | E.Eql lt ->
      List.fold_left
        (fun env t-> add_term env facts t ex) env  lt
    | E.Distinct lt
    | E.Builtin (_, _, lt) ->
      let env =
        List.fold_left
          (fun env t-> add_term env facts t ex)
          env  lt
      in
      let lvs = concat_leaves env.uf lt in (* A verifier *)
      List.fold_left (* add Distinct and Builtin to Use *)
        (fun env rx ->
           let st, sa = Use.find rx env.use in
           { env with
             use = Use.add rx (st,SetA.add (a, ex) sa) env.use }
        ) env lvs

  let semantic_view env (a, ex, orig) facts =
    match (a: r Sig_rel.literal) with
    | LTerm a -> (* Over terms: add terms + term_canonical_view *)
      let env = add env facts a ex in
      let sa, ex = term_canonical_view env a ex in
      env, (sa, Some a, ex, orig)

    | LSem sa ->
      match sa with
      | A.Builtin _ -> (* we put it in canonical form for FM *)
        let sa, ex = canonical_view env sa ex in
        env, (sa, None, ex, orig)

      | _ ->
        (* XXX if we do canonical_view for
           A.Distinct, the theory of arrays will get lost *)
        env, (sa, None, ex, orig)

  let assume_eq env facts r1 r2 ex =
    Options.tool_req 3 "TR-CCX-Congruence";
    let env = congruence_closure env facts r1 r2 ex in
    if Options.get_no_contracongru () || X.type_info r1 != Ty.Tbool then env
    else begin
      contra_congruence env facts r1;
      contra_congruence env facts r2;
      env
    end

  let assume_dist env _facts lr ex =
    Options.tool_req 3 "TR-CCX-Distinct";
    if Uf.already_distinct env.uf lr then env
    else  {env with uf = Uf.distinct env.uf lr ex}

  let rec assume_equalities env choices (facts: r Sig_rel.facts) =
    if Q.is_empty facts.equas then env, choices
    else begin
      Debug.facts facts "equalities";
      let e = Q.pop facts.equas in
      Q.push e facts.ineqs; (*XXX also added in touched by congruence_closure*)
      let env, (sa, _, ex, _) =  semantic_view env e facts in
      Debug.assume_literal sa;
      let env = match sa with
        | A.Pred (r1,neg) ->
          let r2, r3 =  if neg then X.bot, X.top else X.top, X.bot in
          if X.hash_cmp r1 r2 = 0 then env
          else
            let env = assume_eq env facts r1 r2 ex in
            assume_dist env facts [r1;r3] ex
        | A.Eq(r1, r2) ->
          if X.hash_cmp r1 r2 = 0 then env
          else assume_eq env facts r1 r2 ex

        | A.Distinct(true, lt) -> (* nary equality *)
          let lt = List.fast_sort X.hash_cmp lt in
          let env, _ = match lt with
            | [] | [_] -> assert false
            | e :: lt ->
              List.fold_left
                (fun (env, u) v ->
                   (if X.hash_cmp u v = 0 then env
                    else assume_eq env facts u v ex), v
                )(env, e) lt
          in
          env
        | _ -> assert false
      in
      assume_equalities env choices facts
    end

  let rec assume_disequalities env choices (facts: r Sig_rel.facts) =
    if Q.is_empty facts.diseqs then env, choices
    else begin
      Debug.facts facts "disequalities";
      let e = Q.pop facts.diseqs in
      Q.push e facts.ineqs;
      let env, (sa, _, ex, orig) = semantic_view env e facts in
      Debug.assume_literal sa;
      let env = match sa with
        | A.Distinct (false, lr) -> assume_dist env facts lr ex
        | A.Distinct (true, _) -> assert false
        | A.Pred _ ->
          Q.push (Literal.LSem sa, ex, orig) facts.equas;
          env
        | _ -> assert false
      in
      if Q.is_empty facts.equas then assume_disequalities env choices facts
      else env, choices (* Return to give priority to equalities *)
    end

  let rec norm_queue env ineqs (facts:r Sig_rel.facts) =
    if Q.is_empty facts.ineqs then env, List.rev ineqs
    else
      let e = Q.pop facts.ineqs in
      let env, e' = semantic_view env e facts in
      let ineqs = e'::ineqs in
      let ineqs =
        match e with
        (* for case-split, to be sure that CS is given
           back to relations *)
        | LSem ra, ex, ((Th_util.CS _ | Th_util.NCS _) as orig) ->
          (ra, None, ex, orig) :: ineqs
        | _ -> ineqs
      in
      norm_queue env ineqs facts

  let add_touched uf acc (facts:r Sig_rel.facts) =
    let acc =
      Util.MI.fold
        (fun _ x acc ->
           let y, ex = Uf.find_r uf x in (*use terms ? *)
           (* PB Here: LR.mkv_eq may swap x and y *)
           ((*LR.mkv_eq x y*) A.Eq(x, y), None, ex, Th_util.Subst) :: acc)
        facts.touched acc
    in
    facts.touched <- Util.MI.empty;
    acc

  let assume_inequalities env choices (facts: r Sig_rel.facts) =
    Options.tool_req 3 "TR-CCX-Builtin";
    if Q.is_empty facts.ineqs then env, choices
    else begin
      Debug.facts facts "inequalities";
      let env, ineqs = norm_queue env [] facts in
      let ineqs = add_touched env.uf ineqs facts in
      let env, l = replay_atom env ineqs in
      List.iter (add_fact facts) l;
      env, List.rev_append l choices
    end

  let rec assume_literals env choices (facts: r Sig_rel.facts) =
    match Q.is_empty facts.equas with
    | false ->
      let env, choices = assume_equalities env choices facts in
      assume_literals env choices facts
    | true ->
      match Q.is_empty facts.diseqs with
      | false ->
        let env, choices = assume_disequalities env choices facts in
        assume_literals env choices facts
      | true ->
        match Q.is_empty facts.ineqs with
        | false ->
          let env, choices = assume_inequalities env choices facts in
          assume_literals env choices facts
        | true -> env, choices


  let theories_instances ~do_syntactic_matching t_match env selector =
    let rel, th_instances =
      Rel.instantiate
        ~do_syntactic_matching t_match env.relation env.uf selector in
    {env with relation=rel}, th_instances

  let add_term env facts t ex =
    let env = add_term env facts t ex in
    env, facts

  let add env facts a ex =
    let env = add env facts a ex in
    env, facts

  (* End: new implementation of add, add_term, assume_literals and all that *)

  let case_split env ~for_model =
    let cs = Rel.case_split env.relation env.uf ~for_model in
    match cs with
    | [] when for_model ->
      let l, uf = Uf.assign_next env.uf in
      (* TODO: Try to not to modify uf in the future. It's currently done only
         to add fresh terms in UF to avoid loops. *)
      l, {env with uf}
    | _ -> cs, env

  let optimizing_objective env o =
    Rel.optimizing_objective env.relation env.uf o

  let query env a =
    let ra, ex_ra = term_canonical_view env a Ex.empty in
    Rel.query env.relation env.uf (ra, Some a, ex_ra, Th_util.Other)

  let new_terms env = Rel.new_terms env.relation

  let class_of env t = Uf.class_of env.uf t

  let are_distinct env t1 t2 = Uf.are_distinct env.uf t1 t2

  let cl_extract env = Uf.cl_extract env.uf

  let get_union_find env = env.uf

  let assume_th_elt env th_elt dep =
    {env with relation = Rel.assume_th_elt env.relation th_elt dep}

  let are_equal env t1 t2 ~init_terms =
    if E.equal t1 t2 then Some (Ex.empty, [])
    else
    if init_terms then
      let facts = empty_facts() in
      let env, facts = add_term env facts t1 Ex.empty in
      let env, facts = add_term env facts t2 Ex.empty in
      try
        let env, _ = assume_literals env [] facts in
        Uf.are_equal env.uf t1 t2 ~added_terms:true
      with Ex.Inconsistent (ex,cl) -> Some (ex, cl)
    else
      Uf.are_equal env.uf t1 t2 ~added_terms:false

  let term_repr env t ~init_term =
    let env =
      if not init_term then env
      else
        let facts = empty_facts() in
        let env, facts = add_term env facts t Ex.empty in
        fst (assume_literals env [] facts) (* may raise Inconsistent *)
    in
    Uf.term_repr env.uf t

  let extract_concrete_model ~prop_model ~declared_names env =
    Uf.extract_concrete_model ~prop_model ~declared_names env.uf
end
