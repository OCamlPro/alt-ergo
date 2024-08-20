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

module E = Expr
module ME = E.Map
module SubstE = Var.Map

let src = Logs.Src.create ~doc:"Matching" __MODULE__
module Log = (val Logs.src_log src : Logs.LOG)

module type S = sig
  type t
  type theory

  val empty : t

  val make:
    max_t_depth:int ->
    Matching_types.info ME.t ->
    E.t list ME.t Symbols.Map.t ->
    Matching_types.trigger_info list ->
    t

  val add_term : Matching_types.term_info -> E.t -> t -> t
  val max_term_depth : t -> int -> t
  val add_triggers :
    Util.matching_env -> t -> (Expr.t * int * Explanation.t) ME.t -> t
  val terms_info : t -> Matching_types.info ME.t * E.t list ME.t Symbols.Map.t
  val query :
    Util.matching_env -> t -> theory ->
    (Matching_types.trigger_info * Matching_types.gsubst list) list

  val reinit_caches : unit -> unit

end

module type Arg = sig
  type t
  val term_repr : t -> E.t -> init_term:bool -> E.t
  val are_equal : t -> E.t -> E.t -> init_terms:bool -> Th_util.answer
  val class_of : t -> E.t -> E.Set.t
end

module Make (X : Arg) : S with type theory = X.t = struct

  type theory = X.t

  type t = {
    fils : E.t list ME.t Symbols.Map.t ;
    info : Matching_types.info ME.t ;
    max_t_depth : int;
    pats : Matching_types.trigger_info list
  }

  exception Echec

  let empty = {
    fils = Symbols.Map.empty ;
    info = ME.empty ;
    pats = [ ];
    max_t_depth = 0;
  }

  let make ~max_t_depth info fils pats = { fils; info; pats; max_t_depth }

  let age_limite = Options.get_age_bound
  (* l'age limite des termes, au dela ils ne sont pas consideres par le
     matching *)

  (*BISECT-IGNORE-BEGIN*)
  module Debug = struct
    open Printer
    let add_term t =
      if Options.get_debug_matching() >= 3 then
        print_dbg
          ~module_name:"Matching" ~function_name:"add_term"
          "add_term:  %a" E.print t

    let matching tr =
      if Options.get_debug_matching() >= 3 then
        print_dbg
          ~module_name:"Matching" ~function_name:"matching"
          "@[<v 0>(multi-)trigger: %a@ \
           ========================================================@]"
          E.print_list tr.E.content

    let match_pats_modulo pat lsubsts =
      if Options.get_debug_matching() >= 3 then
        let print fmt Matching_types.{ sbs; sty; _ } =
          Format.fprintf fmt ">>> sbs= %a | sty= %a@ "
            (SubstE.pp E.print) sbs Ty.print_subst sty
        in
        print_dbg
          ~module_name:"Matching" ~function_name:"match_pats_modulo"
          "@[<v 2>match_pat_modulo: %a  with accumulated substs@ %a@]"
          E.print pat (pp_list_no_space print) lsubsts

    let match_one_pat Matching_types.{ sbs; sty; _ } pat0 =
      if Options.get_debug_matching() >= 3 then
        print_dbg
          ~module_name:"Matching" ~function_name:"match_one_pat"
          "match_pat: %a with subst: sbs= %a | sty= %a"
          E.print pat0 (SubstE.pp E.print) sbs Ty.print_subst sty


    let match_one_pat_against Matching_types.{ sbs; sty; _ } pat0 t =
      if Options.get_debug_matching() >= 3 then
        print_dbg
          ~module_name:"Matching" ~function_name:"match_one_pat_against"
          "@[<v 0>match_pat: %a against term %a@ \
           with subst:  sbs= %a | sty= %a@]"
          E.print pat0
          E.print t
          (SubstE.pp E.print) sbs
          Ty.print_subst sty

    let match_term Matching_types.{ sbs; sty; _ } t pat =
      if Options.get_debug_matching() >= 3 then
        print_dbg
          ~module_name:"Matching" ~function_name:"match_term"
          "I match %a against %a with subst: sbs=%a | sty= %a"
          E.print pat E.print t (SubstE.pp E.print) sbs Ty.print_subst sty

    let match_list Matching_types.{ sbs; sty; _ } pats xs =
      if Options.get_debug_matching() >= 3 then
        print_dbg
          ~module_name:"Matching" ~function_name:"match_list"
          "I match %a against %a with subst: sbs=%a | sty= %a"
          E.print_list pats
          E.print_list xs
          (SubstE.pp E.print) sbs
          Ty.print_subst sty

    let match_class_of t cl =
      if Options.get_debug_matching() >= 3 then
        print_dbg
          ~module_name:"Matching" ~function_name:"match_class_of"
          "class_of (%a) = { %a }"
          E.print t
          (fun fmt -> E.Set.iter (Format.fprintf fmt "%a , " E.print)) cl

    let candidate_substitutions pat_info res =
      let open Matching_types in
      if Options.get_debug_matching () >= 1 then
        print_dbg
          ~module_name:"Matching" ~function_name:"candidate_substitutions"
          "@[<v 2>%3d candidate substitutions for Axiom %a with trigger %a@ "
          (List.length res)
          E.print pat_info.trigger_orig
          E.print_list pat_info.trigger.E.content;
      if Options.get_debug_matching() >= 2 then
        List.iter
          (fun gsbt ->
             print_dbg ~header:false
               ">>> sbs = %a  and  sbty = %a@ "
               (SubstE.pp E.print) gsbt.sbs Ty.print_subst gsbt.sty
          )res

  end
  (*BISECT-IGNORE-END*)

  let infos op_gen op_but t g b env =
    try
      let i = ME.find t env.info in
      op_gen i.age g , op_but i.but b
    with Not_found -> g , b

  let add_term info t env =
    let open Matching_types in
    Debug.add_term t;
    let rec add_rec env t =
      if ME.mem t env.info then env
      else
        let { E.f = f; xs = xs; _ } = E.term_view t in
        let env =
          let map_f =
            try Symbols.Map.find f env.fils with Not_found -> ME.empty in

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
            fils = Symbols.Map.add f (ME.add t xs map_f) env.fils;
            info =
              ME.add t
                { age=g; lem_orig = from_lems; but=b;
                  t_orig = info.term_from_terms }
                env.info
          }
        in
        List.fold_left add_rec env xs
    in
    if info.term_age > age_limite () then env else add_rec env t

  let add_trigger p env = { env with pats = p :: env.pats }

  let all_terms
      f ty env tbox
      ({sbs=s_t; sty=s_ty; gen=g; goal=b;
        s_term_orig=s_torig;
        s_lem_orig = s_lorig}: Matching_types.gsubst) lsbt_acc =
    let open Matching_types in
    Symbols.Map.fold
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

  let add_msymb tbox f t ({ sbs = s_t; _ } as sg : Matching_types.gsubst)
      max_t_depth =
    if SubstE.mem f s_t then
      let s = SubstE.find f s_t in
      if are_equal_full tbox t s == None then raise Echec;
      sg
    else
      let t =
        if (E.depth t) > max_t_depth ||
           Options.get_normalize_instances () then
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
    let ty = E.type_info t in
    if not (Options.get_arith_matching ()) ||
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
      ({ sty = s_ty; gen = g; goal = b; _ } as sg : Matching_types.gsubst)
      pat t =
    Options.exec_thread_yield ();
    Debug.match_term sg t pat;
    let { E.f = f_pat; xs = pats; ty = ty_pat; _ } = E.term_view pat in
    match f_pat with
    |  Symbols.Var v when Var.equal v Var.underscore ->
      begin
        try [ { sg with sty = Ty.matching s_ty ty_pat (E.type_info t) } ]
        with Ty.TypeClash _ -> raise Echec
      end
    | Symbols.Var v ->
      let sb =
        (try
           let s_ty = Ty.matching s_ty ty_pat (E.type_info t) in
           let g',b' = infos max (||) t g b env in
           add_msymb tbox v t
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
          let cl = if mconf.Util.no_ematching then E.Set.singleton t
            else X.class_of tbox t
          in
          Debug.match_class_of t cl;
          let cl =
            E.Set.fold
              (fun t l ->
                 let { E.f = f; xs = xs; ty = ty; _ } = E.term_view t in
                 if Symbols.compare f_pat f = 0 then xs::l
                 else
                   begin
                     match f_pat, ty with
                     | Symbols.Op (Symbols.Record), Ty.Trecord record ->
                       (xs_modulo_records t record) :: l
                     | _ -> l
                   end
              ) cl []
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
    Steps.incr (Steps.Matching);
    Debug.match_one_pat sg pat0;
    let pat = E.apply_subst (sg.sbs, sg.sty) pat0 in
    let { E.f = f; xs = pats; ty = ty; _ } = E.term_view pat in
    match f with
    | Symbols.Var v -> all_terms v ty env tbox sg lsbt_acc
    | _ ->
      let Matching_types.{ sty; gen = g; goal = b; _ } = sg in
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
      try ME.fold f_aux (Symbols.Map.find f env.fils) lsbt_acc
      with Not_found -> lsbt_acc

  let match_pats_modulo mconf env tbox lsubsts pat =
    Debug.match_pats_modulo pat lsubsts;
    List.fold_left (match_one_pat mconf env tbox pat) [] lsubsts

  let matching mconf env tbox pat_info =
    let open Matching_types in
    let pats = pat_info.trigger in
    let pats_list = pats.E.content in
    Debug.matching pats;
    if List.length pats_list > Options.get_max_multi_triggers_size () then
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
          if Options.(get_debug_matching() >= 1 && get_verbose()) then
            Printer.print_dbg
              ~module_name:"Matching" ~function_name:"matching"
              "skip matching for %a : cpt = %d"
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
    Timers.with_timer Timers.M_Match Timers.F_query @@ fun () ->
    query env tbox

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

  let triggers_of, clear_triggers_of_trs_tbl =
    let trs_tbl = HEI.create 101 in
    let triggers_of q mconf =
      match q.E.user_trs with
      | _::_ as l -> l
      | [] ->
        try HEI.find trs_tbl (q.E.main, mconf)
        with Not_found ->
          let trs =
            E.make_triggers q.E.main q.E.binders q.E.kind mconf
          in
          HEI.add trs_tbl (q.E.main, mconf) trs;
          trs
    in
    let clear_triggers_of_trs_tbl () =
      HEI.clear trs_tbl
    in
    triggers_of, clear_triggers_of_trs_tbl

  let backward_triggers, clear_backward_triggers_trs_tbl =
    let trs_tbl = HE.create 101 in
    let backward_triggers q =
      try HE.find trs_tbl q.E.main
      with Not_found ->
        let trs =
          E.resolution_triggers ~is_back:true q
        in
        HE.add trs_tbl q.E.main trs;
        trs
    in
    let clear_backward_triggers_trs_tbl () =
      HE.clear trs_tbl
    in
    backward_triggers, clear_backward_triggers_trs_tbl

  let forward_triggers, clear_forward_triggers_trs_tbl =
    let trs_tbl = HE.create 101 in
    let forward_triggers q =
      try HE.find trs_tbl q.E.main
      with Not_found ->
        let trs =
          E.resolution_triggers ~is_back:false q
        in
        HE.add trs_tbl q.E.main trs;
        trs
    in
    let clear_forward_triggers_trs_tbl () =
      HE.clear trs_tbl
    in
    forward_triggers, clear_forward_triggers_trs_tbl

  let add_triggers mconf env formulas =
    ME.fold
      (fun lem (guard, age, dep) env ->
         match E.form_view lem with
         | E.Lemma ({ E.main = f; name; _ } as q) ->
           let tgs, kind =
             match mconf.Util.backward with
             | Util.Normal   -> triggers_of q mconf, "Normal"
             | Util.Backward -> backward_triggers q, "Backward"
             | Util.Forward  -> forward_triggers q, "Forward"
           in
           if Options.get_debug_triggers () then
             Printer.print_dbg
               ~module_name:"Matching" ~function_name:"add_triggers"
               "@[<v 2>%s triggers of %s are:@ %a@]"
               kind name E.print_triggers tgs;
           List.fold_left
             (fun env tr ->
                let info =
                  Matching_types.{ trigger = tr;
                                   trigger_age = age ;
                                   trigger_orig = lem ;
                                   trigger_formula = f ;
                                   trigger_dep = dep;
                                   trigger_increm_guard = guard
                                 }
                in
                add_trigger info env
             ) env tgs

         | E.Unit _ | E.Clause _ | E.Literal _ | E.Skolem _
         | E.Let _ | E.Iff _ | E.Xor _ -> assert false
      ) formulas env

  let terms_info env = env.info, env.fils

  let reinit_caches () =
    clear_triggers_of_trs_tbl ();
    clear_backward_triggers_trs_tbl ();
    clear_forward_triggers_trs_tbl ();
    reset_cache_refs ()

end
