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

module Sy = Symbols
module E = Expr
module ME = E.Map

module type S = sig
  type t
  type theory

  val empty : t

  val make:
    max_t_depth:int ->
    Matching_types.info Expr.Map.t ->
    Expr.Set.t Symbols.Map.t ->
    Matching_types.trigger_info list ->
    t

  val add_term : term_info -> E.t -> t -> t
  val max_term_depth : t -> int -> t
  val add_triggers :
    Util.matching_env -> t -> (Expr.t * int * Explanation.t) ME.t -> t
  val terms_info : t -> info ME.t * Expr.Set.t Symbols.Map.t
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
    fils : Expr.Set.t Symbols.Map.t;
    (* A map of symbols to the known terms having this symbol as top symbol. *)

    info : info ME.t;
    (* A map of the terms to their information. *)

    max_t_depth : int;
    (* The current maximal depth. This field is used to limit the size of
       the environment. *)

    pats : trigger_info list;
    (* The list of the known annotated triggers. *)
  }

  exception Echec

  let empty = {
    fils = Symbols.Map.empty;
    info = ME.empty;
    pats = [ ];
    max_t_depth = 0;
  }

  let make ~max_t_depth info fils pats = { fils; info; pats; max_t_depth }

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

    let match_pats_modulo pat lsubsts =
      if get_debug_matching() >= 3 then
        let print fmt { sbs; _ } =
          fprintf fmt ">>> sbs= %a@ " Expr.Subst.pp sbs
        in
        print_dbg
          ~module_name:"Matching" ~function_name:"match_pats_modulo"
          "@[<v 2>match_pat_modulo: %a  with accumulated substs@ %a@]"
          E.print pat (pp_list_no_space print) lsubsts

    let match_one_pat { sbs; _ } pat0 =
      if get_debug_matching() >= 3 then
        print_dbg
          ~module_name:"Matching" ~function_name:"match_one_pat"
          "match_pat: %a with subst: %a"
          E.print pat0 Expr.Subst.pp sbs


    let match_one_pat_against { sbs; _ } pat0 t =
      if get_debug_matching() >= 3 then
        print_dbg
          ~module_name:"Matching" ~function_name:"match_one_pat_against"
          "@[<v 0>match_pat: %a against term %a@ \
           with subst: %a@]"
          E.print pat0
          E.print t
          Expr.Subst.pp sbs

    let match_term { sbs; _ } t pat =
      if get_debug_matching() >= 3 then
        print_dbg
          ~module_name:"Matching" ~function_name:"match_term"
          "I match %a against %a with subst: %a"
          E.print pat E.print t Expr.Subst.pp sbs

    let match_args { sbs; _ } pats xs =
      if get_debug_matching() >= 3 then
        print_dbg
          ~module_name:"Matching" ~function_name:"match_list"
          "I match %a against %a with subst: %a"
          E.print_list pats
          E.print_list xs
          Expr.Subst.pp sbs

    let match_class_of t cl =
      if get_debug_matching() >= 3 then
        print_dbg
          ~module_name:"Matching" ~function_name:"match_class_of"
          "class_of (%a) = { %a }"
          E.print t
          (fun fmt -> List.iter (fprintf fmt "%a , " E.print)) cl

    let candidate_substitutions pat_info res =
      if get_debug_matching () >= 1 then
        print_dbg
          ~module_name:"Matching" ~function_name:"candidate_substitutions"
          "@[<v 2>%3d candidate substitutions for Axiom %a with trigger %a@ "
          (List.length res)
          E.print pat_info.trigger_orig
          E.print_list pat_info.trigger.E.content;
      if get_debug_matching() >= 2 then
        List.iter
          (fun gsbt ->
             print_dbg ~header:false
               ">>> %a@ "
               Expr.Subst.pp gsbt.sbs
          )res

  end
  (*BISECT-IGNORE-END*)

  let infos op_gen op_but t g b env =
    try
      let i = ME.find t env.info in
      op_gen i.age g , op_but i.from_goal b
    with Not_found -> g , b

  let rm x lst = List.filter (fun y -> E.compare x y <> 0) lst

  let rec permutations = function
    | [] -> []
    | x :: [] -> [[x]]
    | lst ->
      List.fold_left (fun acc x ->
          acc @ List.map (fun p -> x :: p) (permutations (rm x lst))
        ) [] lst

  let add_term term_info t env =
    Debug.add_term t;
    let rec add_rec env t =
      if ME.mem t env.info then env
      else begin
        match E.term_view t with
        | E.Term { E.f = f; xs = xs; _ } ->
          let env =
            (* Le lemme de provenance est le dernier lemme. *)
            let from_lems =
              List.fold_left
                (fun acc t ->
                   try (ME.find t env.info).lem_orig @ acc
                   with Not_found -> acc
                )
                (match term_info.term_from_formula with
                   None -> []
                 | Some a -> [a]
                )
                term_info.term_from_terms
            in
            (* Retrieve all the known terms whose the top symbol is f. *)
            let map_f =
              try Symbols.Map.find f env.fils with Not_found -> Expr.Set.empty
            in
            let fils = Symbols.Map.add f (Expr.Set.add t map_f) env.fils in
            let info = ME.add t {
                age = term_info.term_age;
                lem_orig = from_lems;
                from_goal = term_info.term_from_goal;
                t_orig = term_info.term_from_terms
              } env.info
            in
            { env with fils; info }
          in
          (* Recursively adding the subterms of the term t. *)
          List.fold_left add_rec env xs
        | E.Not_a_term {is_lit} ->
          (* TODO: Replace it by Util.failwith. *)
          Printer.print_err
            "%a is not a term, is_lit = %b" E.print t is_lit;
          assert false
      end
    in
    (* l'age limite des termes, au dela ils ne sont pas consideres par le
       matching *)
    if term_info.term_age > Options.get_age_bound () then env else add_rec env t

  let add_trigger p env = { env with pats = p :: env.pats }

  let all_terms f ty env tbox annoted_sbs lsbt_acc =
    let sbs_t, sbs_ty = annoted_sbs.sbs in
    Symbols.Map.fold
      (fun _ map_s l ->
         Expr.Set.fold
           (fun t l ->
              try
                let sbs_ty = Ty.matching sbs_ty ty (E.type_info t) in
                let age, from_goal =
                  try
                    let { age; from_goal; _ } = ME.find t env.info in
                    max age annoted_sbs.age, from_goal || annoted_sbs.from_goal
                  with Not_found -> annoted_sbs.age, annoted_sbs.from_goal
                in
                (* With triggers that are variables, always normalize
                   substitutions. *)
                let t = X.term_repr tbox t ~init_term:true in
                let sbs_t = Expr.TSubst.assign f t sbs_t in
                { annoted_sbs with sbs = (sbs_t, sbs_ty);
                                   age;
                                   from_goal;
                                   s_term_orig = t :: annoted_sbs.s_term_orig;
                } :: l
              with Ty.TypeClash _ -> l
           ) map_s l
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

  let add_msymb tbox f t ({ sbs = (sbs_t, sbs_ty); _ } as sg) max_t_depth =
    try
      match Expr.TSubst.apply sbs_t f with
      | s when are_equal_full tbox t s == None -> raise Echec
      | _ -> sg
    with Not_found -> begin
        let t =
          if (E.depth t) > max_t_depth || get_normalize_instances () then
            X.term_repr tbox t ~init_term:true
          else t
        in
        { sg with sbs = (Expr.TSubst.assign f t sbs_t, sbs_ty) }
      end

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

  (* Update the classes according to the equality modulo theory. *)
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

  let minus_of_plus t d ty = [E.mk_plus t d ty; d]

  let linear_arithmetic_matching f_pat pats _ty_pat t =
    match E.term_view t with
    | E.Not_a_term _ -> assert false
    | E.Term { E.ty; _ } ->
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
      ({ sbs = (sbs_t, sbs_ty); _ } as sg) pat t =
    Options.exec_thread_yield ();
    Debug.match_term sg t pat;
    let { E.f = f_pat; xs = pats; ty = ty_pat; _ } =
      match E.term_view pat with
      | E.Not_a_term _ -> assert false
      | E.Term tt -> tt
    in
    let sbs_ty = Ty.matching sbs_ty ty_pat (E.type_info t) in
    match f_pat with
    |  Symbols.Var _ when Symbols.equal f_pat Symbols.underscore ->
      begin
        try [ { sg with sbs = (sbs_t, sbs_ty) } ]
        with Ty.TypeClash _ -> raise Echec
      end
    | Symbols.Var _ ->
      let sb =
        (try
           let age, from_goal = infos max (||) t sg.age sg.from_goal env in
           add_msymb tbox f_pat t
             { sg with sbs = (sbs_t, sbs_ty); age; from_goal }
             env.max_t_depth
         with Ty.TypeClash _ -> raise Echec)
      in
      [sb]
    | _ ->
      try
        let gsb = { sg with sbs = (sbs_t, sbs_ty) } in
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
              ) [] cl
          in
          let cl = filter_classes mconf cl tbox in
          let cl =
            if cl != [] then cl
            else linear_arithmetic_matching f_pat pats ty_pat t
          in
          List.fold_left
            (fun acc xs ->
               try (match_args mconf env tbox gsb pats xs) -@ acc
               with Echec -> acc
            ) [] cl
      with Ty.TypeClash _ -> raise Echec

  and match_args mconf env tbox sg pats xs =
    Debug.match_args sg pats xs;
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
    let pat = Expr.apply_subst sg.sbs pat0 in
    let { E.f = f; xs = pats; ty = ty; _ } =
      match E.term_view pat with
      | E.Not_a_term _ -> assert false
      | E.Term tt -> tt
    in
    match f with
    | Symbols.Var _ -> all_terms f ty env tbox sg lsbt_acc
    | _ ->
      let { sbs = (sbs_t, sbs_ty); age; from_goal; _ } = sg in
      let f_aux ({ xs; _ } as t : Expr.t) lsbt =
        (* maybe put 3 as a rational parameter in the future *)
        let too_big = (E.depth t) > 10000 * env.max_t_depth in
        if too_big then
          lsbt
        else
          try
            Debug.match_one_pat_against sg pat0 t;
            let sbs_ty = Ty.matching sbs_ty ty (E.type_info t) in
            let age, from_goal = infos max (||) t age from_goal env in
            let sg =
              { sg with
                sbs = (sbs_t, sbs_ty); age; from_goal;
                s_term_orig = t :: sg.s_term_orig }
            in
            let aux = match_args mconf env tbox sg pats xs in
            List.rev_append aux lsbt
          with Echec | Ty.TypeClash _ -> lsbt
      in
      try Expr.Set.fold f_aux (Symbols.Map.find f env.fils) lsbt_acc
      with Not_found -> lsbt_acc

  (*  *)
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

  (* Produce a list of candidate substitutions for the annoted trigger
     [pat_info]. The trigger is ignored if its number of terms exceed the value
     of the option [get_max_multi_triggers_size]. *)
  let matching mconf env tbox pat_info =
    let trigger = pat_info.trigger in
    let pats_list = List.stable_sort trig_weight trigger.E.content in
    Debug.matching trigger;
    if List.length pats_list > Options.get_max_multi_triggers_size () then
      []
    else
      let egs = {
        sbs = Expr.Subst.id;
        age = 0;
        from_goal = false;
        s_term_orig = [];
        s_lem_orig = pat_info.trigger_orig;
      }
      in
      match pats_list with
      | []  -> []
      | [_] ->
        let res =
          List.fold_left (match_pats_modulo mconf env tbox) [egs] pats_list in
        Debug.candidate_substitutions pat_info res;
        res
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
          res
        with Exit ->
          if get_debug_matching() >= 1 && get_verbose() then begin
            Printer.print_dbg
              ~module_name:"Matching" ~function_name:"matching"
              "skip matching for %a : cpt = %d"
              E.print pat_info.trigger_orig !cpt
          end;
          []

  let reset_cache_refs () =
    cache_are_equal_light := MT2.empty;
    cache_are_equal_full  := MT2.empty

  let query mconf env tbox =
    reset_cache_refs ();
    try
      let res =
        List.rev_map
          (fun pat_info ->
             pat_info, matching mconf env tbox pat_info
          ) env.pats
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

  (*  [add_triggers mconf env formulas] add to the environment [env] the
      triggers contained in the [formulas]. More precisely, [formulas] is a map
      of lemmas to triplets (guard, age, dep) where [age] is the initial [age]
      of the new trigger. *)
  let add_triggers mconf env formulas =
    ME.fold
      (fun lem (guard, age, dep) env ->
         match E.form_view lem with
         | E.Lemma ({ E.main = f; name; _ } as q) ->
           let tgs, kind =
             match mconf.Util.inst_mode with
             | Util.Normal   -> normal_triggers q mconf, "Normal"
             | Util.Backward -> backward_triggers q, "Backward"
             | Util.Forward  -> forward_triggers q, "Forward"
           in
           if get_debug_triggers () then
             Printer.print_dbg
               ~module_name:"Matching" ~function_name:"add_triggers"
               "@[<v 2>%s triggers of %s are:@ %a@]"
               kind name E.print_triggers tgs;
           List.fold_left
             (fun env tr ->
                let info =
                  { trigger = tr;
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
         | E.Let _ | E.Iff _ | E.Xor _ | E.Not_a_form -> assert false
      ) formulas env

  let terms_info env = env.info, env.fils

end
