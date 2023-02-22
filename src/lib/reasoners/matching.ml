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

module Sy = Symbols
module E = Expr
module ME = E.Map

module type S = sig
  type t

  type theory

  val empty : t

  val make :
    max_t_depth: int ->
    known_terms: Expr.Set.t ->
    known_pats: Expr.trigger list ->
    Expr.Set.t Symbols.Map.t ->
    t

  val add_term : t -> Expr.t -> t
  val max_term_depth : t -> int -> t

  val add_triggers :
    Util.matching_env -> t -> Expr.t list -> t

  val query :
    Util.matching_env -> t -> theory -> Expr.Subst.t list list
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
    (* Map of symbols to the known terms having this symbol as top symbol. *)

    known_terms : Expr.Set.t;
    (* Set of the known terms. *)

    known_pats : Expr.trigger list;
    (* List of the known triggers. *)

    max_t_depth : int;
    (* The current maximal depth. This field is used to limit the size of
       the environment. *)
  }

  exception Echec

  let empty = {
    fils = Symbols.Map.empty;
    known_terms = Expr.Set.empty;
    known_pats = [];
    max_t_depth = 0;
  }

  let make ~max_t_depth ~known_terms ~known_pats fils =
    { fils; known_terms; known_pats; max_t_depth }

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

    let match_pats_modulo pat sbts =
      if get_debug_matching() >= 3 then
        let print fmt sbt =
          fprintf fmt ">>> sbs= %a@ " Expr.Subst.pp sbt
        in
        print_dbg
          ~module_name:"Matching" ~function_name:"match_pats_modulo"
          "@[<v 2>match_pat_modulo: %a  with accumulated substs@ %a@]"
          E.print pat (pp_list_no_space print) sbts

    let match_one_pat sbt pat0 =
      if get_debug_matching() >= 3 then
        print_dbg
          ~module_name:"Matching" ~function_name:"match_one_pat"
          "match_pat: %a with subst: %a"
          E.print pat0 Expr.Subst.pp sbt


    let match_one_pat_against sbt pat0 t =
      if get_debug_matching() >= 3 then
        print_dbg
          ~module_name:"Matching" ~function_name:"match_one_pat_against"
          "@[<v 0>match_pat: %a against term %a@ \
           with subst: %a@]"
          E.print pat0
          E.print t
          Expr.Subst.pp sbt

    let match_term sbt t pat =
      if get_debug_matching() >= 3 then
        print_dbg
          ~module_name:"Matching" ~function_name:"match_term"
          "I match %a against %a with subst: %a"
          E.print pat E.print t Expr.Subst.pp sbt

    let match_list sbt pats terms =
      if get_debug_matching() >= 3 then
        print_dbg
          ~module_name:"Matching" ~function_name:"match_list"
          "I match %a against %a with subst: %a"
          E.print_list pats
          E.print_list terms
          Expr.Subst.pp sbt

    let match_class_of t cl =
      if get_debug_matching() >= 3 then
        print_dbg
          ~module_name:"Matching" ~function_name:"match_class_of"
          "class_of (%a) = { %a }"
          E.print t
          (fun fmt -> List.iter (fprintf fmt "%a , " E.print)) cl

    let candidate_substitutions trigger res =
      if get_debug_matching () >= 1 then
        print_dbg
          ~module_name:"Matching" ~function_name:"candidate_substitutions"
          "@[<v 2>%3d candidate substitutions for Axiom %%a with trigger %a@ "
          (List.length res)
          (*E.print pat_info.trigger_orig*)
          E.print_list trigger.E.content;
      if get_debug_matching() >= 2 then
        List.iter (print_dbg ~header:false ">>> %a@ " Expr.Subst.pp) res

  end
  (*BISECT-IGNORE-END*)

  let rm x lst = List.filter (fun y -> E.compare x y <> 0) lst

  let rec permutations = function
    | [] -> []
    | x :: [] -> [[x]]
    | lst ->
      List.fold_left (fun acc x ->
          acc @ List.map (fun p -> x :: p) (permutations (rm x lst))
        ) [] lst

  let add_term env t =
    Debug.add_term t;
    let rec add_rec env t =
      if Expr.Set.mem t env.known_terms then env
      else begin
        match E.term_view t with
        | E.Term { E.f = f; xs = xs; _ } ->
          let env =
            (* Retrieve all the known terms whose the top symbol is f. *)
            let map_f =
              try Symbols.Map.find f env.fils with Not_found -> Expr.Set.empty
            in
            let fils = Symbols.Map.add f (Expr.Set.add t map_f) env.fils in
            let known_terms = Expr.Set.add t env.known_terms in
            { env with fils; known_terms }
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
    add_rec env t
  (* l'age limite des termes, au dela ils ne sont pas consideres par le
     matching *)
  (*if term_info.term_age > Options.get_age_bound () then env
    else add_rec env t*)

  let all_terms f ty env tbox (sbt_t, sbt_ty) lsbt_acc =
    Symbols.Map.fold
      (fun _ map_s l ->
         Expr.Set.fold
           (fun t l ->
              try
                let sbt_ty = Ty.matching sbt_ty ty (E.type_info t) in
                (* With triggers that are variables, always normalize
                   substitutions. *)
                let t = X.term_repr tbox t ~init_term:true in
                let sbt_t = Expr.TSubst.assign f t sbt_t in
                (sbt_t, sbt_ty) :: l
              with Ty.TypeClash _ -> l
           ) map_s l
      ) env.fils lsbt_acc

  module MT2 = Map.Make(struct
      type t = E.t * E.t
      let compare (a, b) (x, y) =
        let c = E.compare a x in if c <> 0 then c else E.compare b y
    end)

  let are_equal, reset_cache_refs =
    (* These references are reset before and after each call to query.
       If some intermediate functions are exported in the future, the code
       should be adapted. *)
    let cache_light = ref MT2.empty in
    let cache_full  = ref MT2.empty in
    (fun tbox t s ~(mode: [`Light | `Full ]) ->
       let cache, init_terms =
         match mode with
         | `Light -> cache_light, false
         | `Full  -> cache_full,  true
       in
       try MT2.find (t, s) !cache
       with Not_found ->
         let res = X.are_equal tbox t s ~init_terms |> Option.is_some in
         cache := MT2.add (t, s) res (MT2.add (s, t) res !cache);
         res
    ),
    (fun () ->
       cache_light := MT2.empty;
       cache_full  := MT2.empty
    )

  let add_msymb tbox f t (sbt_t, sbt_ty) max_t_depth =
    try
      match Expr.TSubst.apply sbt_t f with
      | s when are_equal ~mode:`Full tbox t s -> raise Echec
      | _ -> (sbt_t, sbt_ty)
    with Not_found -> begin
        let t =
          if (E.depth t) > max_t_depth || get_normalize_instances () then
            X.term_repr tbox t ~init_term:true
          else t
        in
        (Expr.TSubst.assign f t sbt_t, sbt_ty)
      end

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

  let rec match_term mconf env tbox ((sbt_t, sbt_ty) as sbt) pat t =
    Options.exec_thread_yield ();
    Debug.match_term sbt t pat;
    let { E.xs = pat_args; _ } =
      match E.term_view pat with
      | E.Not_a_term _ -> assert false
      | E.Term tt -> tt
    in
    let sbt_ty = Ty.matching sbt_ty pat.ty (E.type_info t) in
    let sbt = (sbt_t, sbt_ty) in
    match pat.f with
    | Symbols.Var _ when Symbols.equal pat.f Symbols.underscore -> [sbt]
    | Symbols.Var _ ->
      [add_msymb tbox pat.f t sbt env.max_t_depth]
    | _ ->
      try
        if E.is_ground pat && are_equal ~mode:`Light tbox pat t then [sbt]
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
                 if Symbols.compare pat.f f = 0 then xs :: l
                 else
                   begin
                     match pat.f, ty with
                     | Symbols.Op (Symbols.Record), Ty.Trecord record ->
                       (xs_modulo_records t record) :: l
                     | _ -> l
                   end
              ) [] cl
          in
          let cl = filter_classes mconf cl tbox in
          let cl =
            if cl != [] then cl
            else linear_arithmetic_matching pat.f pat_args pat.ty t
          in
          List.fold_left
            (fun acc xs ->
               try (match_list mconf env tbox sbt pat_args xs) @ acc
               with Echec -> acc
            ) [] cl
      with Ty.TypeClash _ -> raise Echec

  and match_list mconf env tbox sbt pats terms =
    Debug.match_list sbt pats terms;
    try
      List.fold_left2
        (fun sb_l pat arg ->
           List.fold_left
             (fun acc sg ->
                let aux = match_term mconf env tbox sg pat arg in
                (*match aux with [] -> raise Echec | _  -> BUG !! *)
                List.rev_append aux acc
             ) [] sb_l
        ) [sbt] pats terms
    with Invalid_argument _ -> raise Echec

  let match_one_pat mconf env tbox pat lsbt_acc ((sbt_t, sbt_ty) as sbt) =
    Steps.incr (Steps.Matching);
    Debug.match_one_pat sbt pat;
    let pat = Expr.apply_subst sbt pat in
    let { E.f = f; xs = pat_args; ty = ty; _ } =
      match E.term_view pat with
      | E.Not_a_term _ -> assert false
      | E.Term tt -> tt
    in
    match f with
    | Symbols.Var _ -> all_terms f ty env tbox sbt lsbt_acc
    | _ ->
      let f_aux ({ xs = args; _ } as t : Expr.t) lsbt =
        (* maybe put 3 as a rational parameter in the future *)
        let too_big = (E.depth t) > 10000 * env.max_t_depth in
        if too_big then
          lsbt
        else
          try
            Debug.match_one_pat_against sbt pat t;
            let sbt_ty = Ty.matching sbt_ty ty (E.type_info t) in
            let aux = match_list mconf env tbox (sbt_t, sbt_ty) pat_args args in
            List.rev_append aux lsbt
          with Echec | Ty.TypeClash _ -> lsbt
      in
      try Expr.Set.fold f_aux (Symbols.Map.find f env.fils) lsbt_acc
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

  (* Produce a list of candidate substitutions for the annoted trigger
     [pat_info]. The trigger is ignored if its number of terms exceed the value
     of the option [get_max_multi_triggers_size]. *)
  let matching mconf env tbox trigger =
    let pats = List.stable_sort trig_weight trigger.E.content in
    Debug.matching trigger;
    if List.length pats > Options.get_max_multi_triggers_size () then []
    else
      match pats with
      | []  -> []
      | [_] ->
        let res =
          List.fold_left (match_pats_modulo mconf env tbox) [Expr.Subst.id]
            pats
        in
        Debug.candidate_substitutions trigger res;
        res
      | _ ->
        let cpt = ref 1 in
        try
          List.iter
            (fun pat ->
               cpt := !cpt * List.length
                        (match_pats_modulo mconf env tbox [Expr.Subst.id] pat);
               (* TODO: put an adaptive limit *)
               if !cpt = 0 || !cpt > 10_000 then raise Exit
            ) (List.rev pats);
          let res =
            List.fold_left (match_pats_modulo mconf env tbox)
              [Expr.Subst.id] pats
          in
          Debug.candidate_substitutions trigger res;
          res
        with Exit ->
          if get_debug_matching() >= 1 && get_verbose() then begin
            Printer.print_dbg
              ~module_name:"Matching" ~function_name:"matching"
              "skip matching for %%a : cpt = %d"
              !cpt
          end;
          []

  let query mconf env tbox =
    reset_cache_refs ();
    try
      let res = List.rev_map (matching mconf env tbox) env.known_pats in
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

  let add_trigger env trigger =
    { env with known_pats = trigger :: env.known_pats }

  (*  [add_triggers mconf env formulas] add to the environment [env] the
      triggers contained in the [formulas]. More precisely, [formulas] is a map
      of lemmas to triplets (guard, age, dep) where [age] is the initial [age]
      of the new trigger. *)
  let add_triggers mconf =
    List.fold_left
      (fun env lem ->
         match E.form_view lem with
         | E.Lemma ({ name; _ } as q) ->
           let trs, kind =
             match mconf.Util.inst_mode with
             | Util.Normal   -> normal_triggers q mconf, "Normal"
             | Util.Backward -> backward_triggers q, "Backward"
             | Util.Forward  -> forward_triggers q, "Forward"
           in
           if get_debug_triggers () then
             Printer.print_dbg
               ~module_name:"Matching" ~function_name:"add_triggers"
               "@[<v 2>%s triggers of %s are:@ %a@]"
               kind name E.print_triggers trs;
           List.fold_left add_trigger env trs

         | E.Unit _ | E.Clause _ | E.Literal _ | E.Skolem _
         | E.Let _ | E.Iff _ | E.Xor _ | E.Not_a_form -> assert false
      )

end
