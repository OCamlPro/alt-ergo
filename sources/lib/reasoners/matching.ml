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
open Matching_types

module E = Expr
module ME = E.Map
module SubstE = Symbols.Map


module type S = sig
  type t
  type theory

  val empty : t

  val make:
    max_t_depth:int ->
    Matching_types.info ME.t ->
    E.t list ME.t SubstE.t ->
    Matching_types.trigger_info list ->
    t

  val add_term : term_info -> E.t -> t -> t
  val max_term_depth : t -> int -> t
  val add_triggers :
    Util.matching_env -> t -> (int * Explanation.t) ME.t -> t
  val terms_info : t -> info ME.t * E.t list ME.t SubstE.t
  val query :
    Util.matching_env -> t -> theory -> (trigger_info * gsubst list) list

end

module type Arg = sig
  type t
  val term_repr : t -> E.t -> init_term:bool -> E.t
  val are_equal : t -> E.t -> E.t -> init_terms:bool -> Th_util.answer
  val class_of : t -> E.t -> E.t list
end

module Make (X : Arg) : S with type theory = X.t = struct

  type theory = X.t

  type t = {
    fils : E.t list ME.t SubstE.t ;
    info : info ME.t ;
    max_t_depth : int;
    pats : trigger_info list
  }

  exception Echec

  let empty = {
    fils = SubstE.empty ;
    info = ME.empty ;
    pats = [ ];
    max_t_depth = 0;
  }

  let make ~max_t_depth info fils pats = { fils; info; pats; max_t_depth }

  let age_limite = Options.age_bound
  (* l'age limite des termes, au dela ils ne sont pas consideres par le
     matching *)

  (*BISECT-IGNORE-BEGIN*)
  module Debug = struct

    let add_term t =
      if debug_matching() >= 3 then
        fprintf fmt "[matching] add_term:  %a@." E.print t

    let matching tr =
      if debug_matching() >= 3 then begin
        fprintf fmt "@.[matching] (multi-)trigger: %a@."
          E.print_list tr.E.content;
        fprintf fmt "========================================================@."
      end

    let match_pats_modulo pat lsubsts =
      if debug_matching() >= 3 then begin
        fprintf fmt "@.match_pat_modulo: %a  with accumulated substs@."
          E.print pat;
        List.iter (fun { sbs; sty; _ } ->
            fprintf fmt ">>> sbs= %a | sty= %a@."
              (SubstE.print E.print) sbs Ty.print_subst sty
          )lsubsts
      end

    let match_one_pat { sbs; sty; _ } pat0 =
      if debug_matching() >= 3 then
        fprintf fmt "@.match_pat: %a  with subst:  sbs= %a | sty= %a @."
          E.print pat0 (SubstE.print E.print) sbs Ty.print_subst sty


    let match_one_pat_against { sbs; sty; _ } pat0 t =
      if debug_matching() >= 3 then
        fprintf fmt
          "@.match_pat: %a  against term %a@.with subst:  sbs= %a | sty= %a @."
          E.print pat0
          E.print t
          (SubstE.print E.print) sbs
          Ty.print_subst sty

    let match_term { sbs; sty; _ } t pat =
      if debug_matching() >= 3 then
        fprintf fmt
          "[match_term] I match %a against %a with subst: sbs=%a | sty= %a@."
          E.print pat E.print t (SubstE.print E.print) sbs Ty.print_subst sty

    let match_list { sbs; sty; _ } pats xs =
      if debug_matching() >= 3 then
        fprintf fmt
          "@.[match_list] I match %a against %a with subst: sbs=%a | sty= %a@."
          E.print_list pats
          E.print_list xs
          (SubstE.print E.print) sbs
          Ty.print_subst sty

    let match_class_of t cl =
      if debug_matching() >= 3 then
        fprintf fmt "class_of (%a)  = { %a }@."
          E.print t
          (fun fmt -> List.iter (fprintf fmt "%a , " E.print)) cl

    let candidate_substitutions pat_info res =
      if debug_matching() >= 1 then begin
        fprintf fmt "[Matching.matching]@.";
        fprintf fmt "%3d candidate substitutions for Axiom %a with trigger %a@."
          (List.length res)
          E.print pat_info.trigger_orig
          E.print_list pat_info.trigger.E.content;
        if debug_matching() >= 2 then
          List.iter
            (fun gsbt ->
               fprintf fmt " >>> sbs = %a  and  sbty = %a@."
                 (SubstE.print E.print) gsbt.sbs Ty.print_subst gsbt.sty
            )res

      end
  end
  (*BISECT-IGNORE-END*)

  let infos op_gen op_but t g b env =
    try
      let i = ME.find t env.info in
      op_gen i.age g , op_but i.but b
    with Not_found -> g , b

  let add_term info t env =
    Debug.add_term t;
    let rec add_rec env t =
      if ME.mem t env.info then env
      else
        match E.term_view t with
        | E.Term { E.f = f; xs = xs; _ } ->
          let env =
            let map_f =
              try SubstE.find f env.fils with Not_found -> ME.empty in

            (* - l'age d'un terme est le min entre l'age passe en argument
               et l'age dans la map
               - un terme est en lien avec le but de la PO seulement s'il
                 ne peut etre produit autrement (d'ou le &&)
               - le lemme de provenance est le dernier lemme
            *)
            let g, b =
              infos min (&&) t info.term_age info.term_from_goal env in
            let from_lems =
              List.fold_left
                (fun acc t ->
                   try (ME.find t env.info).lem_orig @ acc
                   with Not_found -> acc)
                (match info.term_from_formula with None -> [] | Some a -> [a])
                info.term_from_terms
            in
            { env with
              fils = SubstE.add f (ME.add t xs map_f) env.fils;
              info =
                ME.add t
                  { age=g; lem_orig = from_lems; but=b;
                    t_orig = info.term_from_terms }
                  env.info
            }
          in
          List.fold_left add_rec env xs
        | E.Not_a_term {is_lit} ->
          fprintf fmt "%a is not a term, is_lit = %b@." E.print t is_lit;
          assert false
    in
    if info.term_age > age_limite () then env else add_rec env t

  let add_trigger p env = { env with pats = p :: env.pats }

  let all_terms
      f ty env tbox
      {sbs=s_t; sty=s_ty; gen=g; goal=b;
       s_term_orig=s_torig;
       s_lem_orig = s_lorig} lsbt_acc =
    SubstE.fold
      (fun _ s l ->
         ME.fold
           (fun t _ l ->
              try
                let s_ty = Ty.matching s_ty ty (E.type_info t) in
                let ng , but =
                  try
                    let { age = ng; but = bt; _ } =
                      ME.find t env.info
                    in
                    max ng g , bt || b
                  with Not_found -> g , b
                in
                (* with triggers that are variables, always normalize substs *)
                let t = X.term_repr tbox t ~init_term:true in
                { sbs = SubstE.add f t s_t;
                  sty = s_ty;
                  gen = ng;
                  goal = but;
                  s_term_orig = t :: s_torig;
                  s_lem_orig = s_lorig;
                }::l
              with Ty.TypeClash _ -> l
           ) s l
      ) env.fils lsbt_acc


  module T2 = struct
    type t = E.t * E.t
    let compare (a, b) (x, y) =
      let c = E.compare a x in if c <> 0 then c else E.compare b y
  end

  module MT2 = Map.Make(T2)

  let wrap_are_equal_generic tbox t s add_terms cache_are_eq_gen =
    try MT2.find (t, s) !cache_are_eq_gen
    with Not_found ->
      let res = X.are_equal tbox t s ~init_terms:add_terms in
      cache_are_eq_gen :=
        MT2.add (t, s) res (MT2.add (s, t) res !cache_are_eq_gen);
      res

  (* These references are reset before and after each call to query.
     If some intermediate functions are exported in the future, the code
     should be adapted. *)
  let cache_are_equal_light = ref MT2.empty
  let cache_are_equal_full  = ref MT2.empty

  let are_equal_light tbox t s =
    wrap_are_equal_generic tbox t s false cache_are_equal_light

  let are_equal_full tbox t s =
    wrap_are_equal_generic tbox t s true cache_are_equal_full

  let add_msymb tbox f t ({ sbs = s_t; _ } as sg) max_t_depth =
    if SubstE.mem f s_t then
      let s = SubstE.find f s_t in
      if are_equal_full tbox t s == None then raise Echec;
      sg
    else
      let t =
        if (E.depth t) > max_t_depth || normalize_instances () then
          X.term_repr tbox t ~init_term:true
        else t
      in
      {sg with sbs=SubstE.add f t s_t}

  let (-@) l1 l2 =
    match l1, l2 with
    | [], _  -> l2
    | _ , [] -> l1
    | _ -> List.fold_left (fun acc e -> e :: acc) l2 (List.rev l1)

  let xs_modulo_records t { Ty.lbs; _  } =
    List.rev
      (List.rev_map
         (fun (hs, ty) ->
            E.mk_term (Symbols.Op (Symbols.Access hs)) [t] ty) lbs)

  module SLE = (* sets of lists of terms *)
    Set.Make(struct
      type t = E.t list
      let compare l1 l2 =
        try
          List.iter2
            (fun t1 t2 ->
               let c = E.compare t1 t2 in
               if c <> 0 then raise (Util.Cmp c)
            ) l1 l2;
          0
        with Invalid_argument _ ->
          List.length l1 - List.length l2
           | Util.Cmp n -> n
    end)

  let filter_classes mconf cl tbox =
    if mconf.Util.no_ematching then cl
    else
      let mtl =
        List.fold_left
          (fun acc xs ->
             let xs =
               List.rev
                 (List.rev_map
                    (fun t -> X.term_repr tbox t ~init_term:false) xs)
             in
             SLE.add xs acc
          ) SLE.empty cl
      in
      SLE.elements mtl

  let plus_of_minus t d ty =
    [E.mk_term (Symbols.Op Symbols.Minus) [t; d] ty ; d]

  let minus_of_plus t d ty =
    [E.mk_term (Symbols.Op Symbols.Plus)  [t; d] ty ; d]

  let linear_arithmetic_matching f_pat pats _ty_pat t =
    match E.term_view t with
    | E.Not_a_term _ -> assert false
    | E.Term { E.ty; _ } ->
      if not (Options.arith_matching ()) ||
         ty != Ty.Tint && ty != Ty.Treal then []
      else
        match f_pat, pats with
        | Symbols.Op Symbols.Plus, [p1; p2] ->
          if E.is_ground p2 then [plus_of_minus t p2 ty]
          else if E.is_ground p1 then [plus_of_minus t p1 ty] else []

        | Symbols.Op Symbols.Minus, [p1; p2] ->
          if E.is_ground p2 then [minus_of_plus t p2 ty]
          else if E.is_ground p1 then [minus_of_plus t p1 ty] else []
        | _ -> []

  let rec match_term mconf env tbox
      ({ sty = s_ty; gen = g; goal = b; _ } as sg) pat t =
    Options.exec_thread_yield ();
    Debug.match_term sg t pat;
    let { E.f = f_pat; xs = pats; ty = ty_pat; _ } =
      match E.term_view pat with
      | E.Not_a_term _ -> assert false
      | E.Term tt -> tt
    in
    match f_pat with
    |	 Symbols.Var _ when Symbols.equal f_pat Symbols.underscore ->
      begin
        try [ { sg with sty = Ty.matching s_ty ty_pat (E.type_info t) } ]
        with Ty.TypeClash _ -> raise Echec
      end
    |	Symbols.Var _ ->
      let sb =
        (try
           let s_ty = Ty.matching s_ty ty_pat (E.type_info t) in
           let g',b' = infos max (||) t g b env in
           add_msymb tbox f_pat t
             { sg with sty=s_ty; gen=g'; goal=b' }
             env.max_t_depth
         with Ty.TypeClash _ -> raise Echec)
      in
      [sb]
    | _ ->
      try
        let s_ty = Ty.matching s_ty ty_pat (E.type_info t) in
        let gsb = { sg with sty = s_ty } in
        if E.is_ground pat &&
           are_equal_light tbox pat t != None then
          [gsb]
        else
          let cl = if mconf.Util.no_ematching then [t]
            else X.class_of tbox t
          in
          Debug.match_class_of t cl;
          let cl =
            List.fold_left
              (fun l t ->
                 let { E.f = f; xs = xs; ty = ty; _ } =
                   match E.term_view t with
                   | E.Not_a_term _ -> assert false
                   | E.Term tt -> tt
                 in
                 if Symbols.compare f_pat f = 0 then xs::l
                 else
                   begin
                     match f_pat, ty with
                     | Symbols.Op (Symbols.Record), Ty.Trecord record ->
                       (xs_modulo_records t record) :: l
                     | _ -> l
                   end
              )[] cl
          in
          let cl = filter_classes mconf cl tbox in
          let cl =
            if cl != [] then cl
            else linear_arithmetic_matching f_pat pats ty_pat t
          in
          List.fold_left
            (fun acc xs ->
               try (match_list mconf env tbox gsb pats xs) -@ acc
               with Echec -> acc
            ) [] cl
      with Ty.TypeClash _ -> raise Echec

  and match_list mconf env tbox sg pats xs =
    Debug.match_list sg pats xs;
    try
      List.fold_left2
        (fun sb_l pat arg ->
           List.fold_left
             (fun acc sg ->
                let aux = match_term mconf env tbox sg pat arg in
                (*match aux with [] -> raise Echec | _  -> BUG !! *)
                List.rev_append aux acc
             ) [] sb_l
        ) [sg] pats xs
    with Invalid_argument _ -> raise Echec

  let match_one_pat mconf env tbox pat0 lsbt_acc sg =
    Debug.match_one_pat sg pat0;
    let pat = E.apply_subst (sg.sbs, sg.sty) pat0 in
    let { E.f = f; xs = pats; ty = ty; _ } =
      match E.term_view pat with
      | E.Not_a_term _ -> assert false
      | E.Term tt -> tt
    in
    match f with
    | Symbols.Var _ -> all_terms f ty env tbox sg lsbt_acc
    | _ ->
      let { sty; gen = g; goal = b; _ } = sg in
      let f_aux t xs lsbt =
        (* maybe put 3 as a rational parameter in the future *)
        let too_big = (E.depth t) > 3 * env.max_t_depth in
        if too_big then lsbt
        else
          try
            Debug.match_one_pat_against sg pat0 t;
            let s_ty = Ty.matching sty ty (E.type_info t) in
            let gen, but = infos max (||) t g b env in
            let sg =
              { sg with
                sty = s_ty; gen = gen; goal = but;
                s_term_orig = t::sg.s_term_orig }
            in
            let aux = match_list mconf env tbox sg pats xs in
            List.rev_append aux lsbt
          with Echec | Ty.TypeClash _ -> lsbt
      in
      try ME.fold f_aux (SubstE.find f env.fils) lsbt_acc
      with Not_found -> lsbt_acc

  let match_pats_modulo mconf env tbox lsubsts pat =
    Debug.match_pats_modulo pat lsubsts;
    List.fold_left (match_one_pat mconf env tbox pat) [] lsubsts

  let trig_weight s t =
    match E.term_view s, E.term_view t with
    | E.Not_a_term _, _ | _, E.Not_a_term _ -> assert false
    | E.Term { E.f = Symbols.Name _; _ },
      E.Term { E.f = Symbols.Op _; _ }   -> -1
    | E.Term { E.f = Symbols.Op _; _ },
      E.Term { E.f = Symbols.Name _; _ } -> 1
    | _ -> (E.depth t) - (E.depth s)


  let matching mconf env tbox pat_info =
    let pats = pat_info.trigger in
    let pats_list = List.stable_sort trig_weight pats.E.content in
    Debug.matching pats;
    if List.length pats_list > Options.max_multi_triggers_size () then
      pat_info, []
    else
      let egs =
        { sbs = SubstE.empty;
          sty = Ty.esubst;
          gen = 0;
          goal = false;
          s_term_orig = [];
          s_lem_orig = pat_info.trigger_orig;
        }
      in
      match pats_list with
      | []  -> pat_info, []
      | [_] ->
        let res =
          List.fold_left (match_pats_modulo mconf env tbox) [egs] pats_list in
        Debug.candidate_substitutions pat_info res;
        pat_info, res
      | _ ->
        let cpt = ref 1 in
        try
          List.iter
            (fun pat ->
               cpt := !cpt *
                      List.length (match_pats_modulo mconf env tbox [egs] pat);
               (* TODO: put an adaptive limit *)
               if !cpt = 0 || !cpt > 10_000 then raise Exit
            ) (List.rev pats_list);
          let res =
            List.fold_left (match_pats_modulo mconf env tbox) [egs] pats_list
          in
          Debug.candidate_substitutions pat_info res;
          pat_info, res
        with Exit ->
          if verbose() then
            fprintf fmt "@.skip matching for %a : cpt = %d@."
              E.print pat_info.trigger_orig !cpt;
          pat_info, []

  let reset_cache_refs () =
    cache_are_equal_light := MT2.empty;
    cache_are_equal_full  := MT2.empty

  let query mconf env tbox =
    reset_cache_refs ();
    try
      let res = List.rev_map (matching mconf env tbox) env.pats in
      reset_cache_refs ();
      res
    with e ->
      reset_cache_refs ();
      raise e

  let query env tbox =
    if Options.timers() then
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

  let triggers_of =
    let trs_tbl = HEI.create 101 in
    fun q mconf ->
      match q.E.user_trs with
      | _::_ as l -> l
      | [] ->
        try HEI.find trs_tbl (q.E.main, mconf)
        with Not_found ->
          let trs = E.make_triggers q.E.main q.E.binders q.E.kind mconf in
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

  let add_triggers mconf env formulas =
    ME.fold
      (fun lem (age, dep) env ->
         match E.form_view lem with
         | E.Lemma ({ E.main = f; name; _ } as q) ->
           let tgs =
             match mconf.Util.backward with
             | Util.Normal   -> triggers_of q mconf
             | Util.Backward -> backward_triggers q
             | Util.Forward  -> forward_triggers q
           in
           if Options.debug_triggers () then
             fprintf fmt "[expr] triggers of %s are: %a@."
               name E.print_triggers tgs;
           List.fold_left
             (fun env tr ->
                let info =
                  { trigger = tr;
                    trigger_age = age ;
                    trigger_orig = lem ;
                    trigger_formula = f ;
                    trigger_dep = dep}
                in
                add_trigger info env
             ) env tgs

         | E.Unit _ | E.Clause _ | E.Literal _ | E.Skolem _
         | E.Let _ | E.Iff _ | E.Xor _ | E.Not_a_form -> assert false
      ) formulas env

  let terms_info env = env.info, env.fils

end
