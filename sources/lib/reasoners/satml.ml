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

open Format
open Options

module A = Literal.LT
module Atom = Satml_types.Atom
module FF = Satml_types.Flat_Formula
open Atom

module Ex = Explanation

exception Sat
exception Unsat of clause list option
exception Restart

let vraie_form = Formula.vrai


module type SAT_ML = sig
  (*module Make (Dummy : sig end) : sig*)
  type th
  type t

  val solve : t -> unit

  val set_new_proxies :
    t -> (Atom.atom * Atom.atom list * bool) Util.MI.t -> unit

  val new_vars :
    t ->
    nbv : int -> (* nb made vars *)
    var list ->
    atom list list -> atom list list ->
    atom list list * atom list list

  val assume :
    t ->
    Atom.atom list list -> Atom.atom list list -> Formula.t ->
    cnumber : int ->
    Atom.atom option FF.Map.t -> dec_lvl:int ->
    unit

  val boolean_model : t -> Atom.atom list
  val theory_assumed : t -> Literal.LT.Set.t
  val current_tbox : t -> th
  val set_current_tbox : t -> th -> unit
  val empty : unit -> t

  val reset_steps : unit -> unit
  val get_steps : unit -> int64

  val assume_th_elt : t -> Commands.th_elt -> unit
  val decision_level : t -> int
  val cancel_until : t -> int -> unit

  val update_lazy_cnf :
    t ->
    do_bcp : bool ->
    Atom.atom option FF.Map.t -> dec_lvl:int -> unit
  val exists_in_lazy_cnf : t -> FF.t -> bool

  val known_lazy_formulas : t -> int FF.Map.t
(*end*)
end

module MFF = FF.Map
module SFF = FF.Set

module Make (Th : Theory.S) : SAT_ML with type th = Th.t = struct

  module Matoms = Map.Make (struct type t = atom let compare = cmp_atom end)

  type th = Th.t
  type t =
      {
      (* si vrai, les contraintes sont deja fausses *)
        mutable is_unsat : bool;

        mutable unsat_core : clause list option;

      (* clauses du probleme *)
        mutable clauses : clause Vec.t;

      (* clauses apprises *)
        mutable learnts : clause Vec.t;

      (* valeur de l'increment pour l'activite des clauses *)
        mutable clause_inc : float;

      (* valeur de l'increment pour l'activite des variables *)
        mutable var_inc : float;

      (* un vecteur des variables du probleme *)
        mutable vars : var Vec.t;

      (* la pile de decisions avec les faits impliques *)
        mutable trail : atom Vec.t;

      (* une pile qui pointe vers les niveaux de decision dans trail *)
        mutable trail_lim : int Vec.t;

      (* Tete de la File des faits unitaires a propager.
	 C'est un index vers le trail *)
        mutable qhead : int;

      (* Nombre des assignements top-level depuis la derniere
         execution de 'simplify()' *)
        mutable simpDB_assigns : int;

      (* Nombre restant de propagations a faire avant la prochaine
         execution de 'simplify()' *)
        mutable simpDB_props : int;

      (* Un tas ordone en fonction de l'activite des variables *)
        mutable order : Iheap.t;

      (* estimation de progressions, mis a jour par 'search()' *)
        mutable progress_estimate : float;

      (* *)
        remove_satisfied : bool;

      (* inverse du facteur d'acitivte des variables, vaut 1/0.999 par defaut *)
        var_decay : float;

      (* inverse du facteur d'activite des clauses, vaut 1/0.95 par defaut *)
        clause_decay : float;

      (* la limite de restart initiale, vaut 100 par defaut *)
        mutable restart_first : int;

      (* facteur de multiplication de restart limite, vaut 1.5 par defaut*)
        restart_inc : float;

      (* limite initiale du nombre de clause apprises, vaut 1/3
         des clauses originales par defaut *)
        mutable learntsize_factor : float;

      (* multiplier learntsize_factor par cette valeur a chaque restart,
         vaut 1.1 par defaut *)
        learntsize_inc : float;

      (* controler la minimisation des clauses conflit, vaut true par defaut *)
        expensive_ccmin : bool;

      (* controle la polarite a choisir lors de la decision *)
        polarity_mode : bool;

        mutable starts : int;

        mutable decisions : int;

        mutable propagations : int;

        mutable conflicts : int;

        mutable clauses_literals : int;

        mutable learnts_literals : int;

        mutable max_literals : int;

        mutable tot_literals : int;

        mutable nb_init_vars : int;

        mutable nb_init_clauses : int;

        mutable model : var Vec.t;

        mutable tenv : Th.t;

        mutable unit_tenv : Th.t;

        mutable tenv_queue : Th.t Vec.t;

        mutable tatoms_queue : atom Queue.t;
        mutable th_tableaux : atom Queue.t;

        mutable cpt_current_propagations : int;

        mutable proxies : (Atom.atom * Atom.atom list * bool) Util.MI.t;

        mutable lazy_cnf :
          (FF.t list MFF.t * FF.t) Matoms.t;

        lazy_cnf_queue :
          (FF.t list MFF.t * FF.t) Matoms.t Vec.t;

        mutable relevants : SFF.t;
        relevants_queue : SFF.t Vec.t;

        mutable ff_lvl : int MFF.t;

        mutable lvl_ff : SFF.t Util.MI.t;
      }

  type conflict_origin =
    | C_none
    | C_bool of clause
    | C_theory of Ex.t

  exception Conflict of clause
  (*module Make (Dummy : sig end) = struct*)

  let steps = ref 0L

  let reset_steps () = steps := 0L
  let get_steps () = !steps

  let empty () =
    {
      is_unsat = false;

      unsat_core = None;

      clauses = Vec.make 0 Atom.dummy_clause;
      (*sera mis a jour lors du parsing*)

      learnts = Vec.make 0 Atom.dummy_clause;
      (*sera mis a jour lors du parsing*)

      clause_inc = 1.;

      var_inc = 1.;

      vars = Vec.make 0 dummy_var; (*sera mis a jour lors du parsing*)

      trail = Vec.make 601 dummy_atom;

      trail_lim = Vec.make 601 (-105);

      qhead = 0;

      simpDB_assigns = -1;

      simpDB_props = 0;

      order = Iheap.init 0; (* sera mis a jour dans solve *)

      progress_estimate = 0.;

      remove_satisfied = true;

      var_decay = 1. /. 0.95;

      clause_decay = 1. /. 0.999;

      restart_first = 100;

      restart_inc = 1.5;

      learntsize_factor = 1. /. 3. ;

      learntsize_inc = 1.1;

      expensive_ccmin = true;

      polarity_mode = false;

      starts = 0;

      decisions = 0;

      propagations = 0;

      conflicts = 0;

      clauses_literals = 0;

      learnts_literals = 0;

      max_literals = 0;

      tot_literals = 0;

      nb_init_vars = 0;

      nb_init_clauses = 0;

      model = Vec.make 0 dummy_var;

      tenv = Th.empty();

      unit_tenv = Th.empty();

      tenv_queue = Vec.make 100 (Th.empty());

      tatoms_queue = Queue.create ();

      th_tableaux = Queue.create ();

      cpt_current_propagations = 0;

      proxies = Util.MI.empty;

      lazy_cnf = Matoms.empty;

      lazy_cnf_queue =
        Vec.make 100
          (Matoms.singleton (faux_atom) (MFF.empty, FF.faux));

      relevants = SFF.empty;
      relevants_queue = Vec.make 100 (SFF.singleton (FF.faux));

      ff_lvl = MFF.empty;

      lvl_ff = Util.MI.empty;
}


(*
  module SA = Set.Make
  (struct
  type t = Atom.atom
  let compare a b = a.Atom.aid - b.Atom.aid
  end)

  module SSA = Set.Make(SA)


  let ssa = ref SSA.empty

  let clause_exists atoms =
  try
(*List.iter
  (fun a -> if a.is_true then raise Exit) atoms;*)
  let sa = List.fold_left (fun s e -> SA.add e s) SA.empty atoms in
  if SSA.mem sa !ssa then true
  else begin
  ssa := SSA.add sa !ssa;
  false
  end
  with Exit -> true

  let f_weight i j =
  let vj = Vec.get env.vars j in
  let vi = Vec.get env.vars i in
(*if vi.sweight <> vj.sweight then vi.sweight < vj.sweight
  else*) vj.weight < vi.weight
*)

  let f_weight env i j =
    Pervasives.(<) (Vec.get env.vars j).weight (Vec.get env.vars i).weight

  let f_filter env i = (Vec.get env.vars i).level < 0

  let insert_var_order env v =
    Iheap.insert (f_weight env) env.order v.vid

  let var_decay_activity env = env.var_inc <- env.var_inc *. env.var_decay

  let clause_decay_activity env =
    env.clause_inc <- env.clause_inc *. env.clause_decay

  let var_bump_activity env v =
    v.weight <- v.weight +. env.var_inc;
    if Pervasives.(>) v.weight 1e100 then begin
      for i = 0 to env.vars.Vec.sz - 1 do
        (Vec.get env.vars i).weight <- (Vec.get env.vars i).weight *. 1e-100
      done;
      env.var_inc <- env.var_inc *. 1e-100;
    end;
    if Iheap.in_heap env.order v.vid then
      Iheap.decrease (f_weight env) env.order v.vid


  let clause_bump_activity env c =
    c.activity <- c.activity +. env.clause_inc;
    if Pervasives.(>) c.activity 1e20 then begin
      for i = 0 to env.learnts.Vec.sz - 1 do
        (Vec.get env.learnts i).activity <-
          (Vec.get env.learnts i).activity *. 1e-20;
      done;
      env.clause_inc <- env.clause_inc *. 1e-20
    end

  let decision_level env = Vec.size env.trail_lim

  let nb_assigns env = Vec.size env.trail
  let nb_clauses env = Vec.size env.clauses
  let nb_learnts env = Vec.size env.learnts
  let nb_vars    env = Vec.size env.vars

  let new_decision_level env =
    env.decisions <- env.decisions + 1;
    Vec.push env.trail_lim (Vec.size env.trail);
    if Options.profiling() then
      Profiling.decision (decision_level env) "<none>";
    Vec.push env.tenv_queue env.tenv; (* save the current tenv *)
    if Options.tableaux_cdcl () then begin
      Vec.push env.lazy_cnf_queue env.lazy_cnf;
      Vec.push env.relevants_queue env.relevants
    end

  let attach_clause env c =
    Vec.push (Vec.get c.atoms 0).neg.watched c;
    Vec.push (Vec.get c.atoms 1).neg.watched c;
    if c.learnt then
      env.learnts_literals <- env.learnts_literals + Vec.size c.atoms
    else
      env.clauses_literals <- env.clauses_literals + Vec.size c.atoms

  let detach_clause env c =
    c.removed <- true;
  (*
    Vec.remove (Vec.get c.atoms 0).neg.watched c;
    Vec.remove (Vec.get c.atoms 1).neg.watched c;
  *)
    if c.learnt then
      env.learnts_literals <- env.learnts_literals - Vec.size c.atoms
    else
      env.clauses_literals <- env.clauses_literals - Vec.size c.atoms

  let remove_clause env c = detach_clause env c

  let satisfied c =
    try
      for i = 0 to Vec.size c.atoms - 1 do
        let a = Vec.get c.atoms i in
        if a.is_true && a.var.level ==0 then raise Exit
      done;
      false
    with Exit -> true

  let unassign_atom a =
    a.is_true <- false;
    a.neg.is_true <- false;
    a.timp <- false;
    a.neg.timp <- false;
    a.var.level <- -1;
    a.var.index <- -1;
    a.var.reason <- None;
    a.var.vpremise <- []

  let enqueue_assigned env a =
    assert (a.is_true || a.neg.is_true);
    assert (a.var.level >= 0);
    Vec.push env.trail a

  let cancel_ff_lvls_until env lvl =
    for i = decision_level env downto lvl + 1 do
      try
        let s = Util.MI.find i env.lvl_ff in
        SFF.iter (fun f' -> env.ff_lvl <- MFF.remove f' env.ff_lvl) s;
        env.lvl_ff <- Util.MI.remove i env.lvl_ff;
      with Not_found -> ()
    done

(* annule tout jusqu'a lvl *exclu*  *)
  let cancel_until env lvl =
    cancel_ff_lvls_until env lvl;
    let repush = ref [] in
    if decision_level env > lvl then begin
      env.qhead <- Vec.get env.trail_lim lvl;
      for c = Vec.size env.trail - 1 downto env.qhead do
        let a = Vec.get env.trail c in
        if Options.minimal_bj () && a.var.level <= lvl then begin
          assert (a.var.level = 0 || a.var.reason != None);
          repush := a :: !repush
        end
        else begin
          unassign_atom a;
          insert_var_order env a.var
        end
      done;
      Queue.clear env.tatoms_queue;
      Queue.clear env.th_tableaux;
      env.tenv <- Vec.get env.tenv_queue lvl; (* recover the right tenv *)
      if Options.tableaux_cdcl () then begin
        env.lazy_cnf <- Vec.get env.lazy_cnf_queue lvl;
        env.relevants <- Vec.get env.relevants_queue lvl;
      end;
      Vec.shrink env.trail ((Vec.size env.trail) - env.qhead) true;
      Vec.shrink env.trail_lim ((Vec.size env.trail_lim) - lvl) true;
      Vec.shrink env.tenv_queue ((Vec.size env.tenv_queue) - lvl) true;
      if Options.tableaux_cdcl () then begin
        Vec.shrink
          env.lazy_cnf_queue ((Vec.size env.lazy_cnf_queue) - lvl) true;
        Vec.shrink env.relevants_queue
          ((Vec.size env.relevants_queue) - lvl) true
          [@ocaml.ppwarning "TODO: try to disable 'fill_with_dummy'"]
      end;
      (try
         let last_dec =
           if Vec.size env.trail_lim = 0 then 0 else Vec.last env.trail_lim in
         env.cpt_current_propagations <- (Vec.size env.trail) - last_dec
       with e -> assert false
      );
    end;
    if Options.profiling() then Profiling.reset_dlevel (decision_level env);
    assert (Vec.size env.trail_lim = Vec.size env.tenv_queue);
    assert (Options.minimal_bj () || (!repush == []));
    List.iter (enqueue_assigned env) !repush

  let rec pick_branch_var env =
    if Iheap.size env.order = 0 then raise Sat;
    let max = Iheap.remove_min (f_weight env) env.order in
    let v = Vec.get env.vars max in
    if v.level>= 0 then begin
      assert (v.pa.is_true || v.na.is_true);
      pick_branch_var env
    end
    else v

  let pick_branch_lit env =
    let v = pick_branch_var env in
    v.na

  let debug_enqueue_level a lvl reason =
    match reason with
    | None -> ()
    | Some c ->
      let maxi = ref min_int in
      for i = 0 to Vec.size c.atoms - 1 do
        let b = Vec.get c.atoms i in
        if not (eq_atom a b) then maxi := max !maxi b.var.level
      done;
      assert (!maxi = lvl)

  let max_level_in_clause c =
    let max_lvl = ref 0 in
    Vec.iter c.atoms (fun a ->
        max_lvl := max !max_lvl a.var.level);
    !max_lvl

  let enqueue env a lvl reason =
    assert (not a.is_true && not a.neg.is_true &&
              a.var.level < 0 && a.var.reason == None && lvl >= 0);
  (* Garder la reason car elle est utile pour les unsat-core *)
  (*let reason = if lvl = 0 then None else reason in*)
    a.is_true <- true;
    a.var.level <- lvl;
    a.var.reason <- reason;
  (*eprintf "enqueue: %a@." Debug.atom a; *)
    Vec.push env.trail a;
    a.var.index <- Vec.size env.trail;
    if Options.enable_assertions() then  debug_enqueue_level a lvl reason

  let progress_estimate env =
    let prg = ref 0. in
    let nbv = to_float (nb_vars env) in
    let lvl = decision_level env in
    let _F = 1. /. nbv in
    for i = 0 to lvl do
      let _beg = if i = 0 then 0 else Vec.get env.trail_lim (i-1) in
      let _end =
        if i=lvl then Vec.size env.trail
        else Vec.get env.trail_lim i in
      prg := !prg +. _F**(to_float i) *. (to_float (_end - _beg))
    done;
    !prg /. nbv

  let check_levels propag_lvl current_lvl =
    assert (propag_lvl <= current_lvl);
    assert (propag_lvl == current_lvl || (Options.minimal_bj ()))

  let best_propagation_level env c =
    let mlvl =
      if Options.minimal_bj () then max_level_in_clause c
      else decision_level env
    in
    check_levels mlvl (decision_level env);
    mlvl

  let propagate_in_clause env a c i watched new_sz =
    let atoms = c.atoms in
    let first = Vec.get atoms 0 in
    if first == a.neg then begin (* le literal faux doit etre dans .(1) *)
      Vec.set atoms 0 (Vec.get atoms 1);
      Vec.set atoms 1 first
    end;
    let first = Vec.get atoms 0 in
    if first.is_true then begin
      (* clause vraie, la garder dans les watched *)
      Vec.set watched !new_sz c;
      incr new_sz;
      if Options.profiling() then Profiling.elim true;
    end
    else
      try (* chercher un nouveau watcher *)
        for k = 2 to Vec.size atoms - 1 do
          let ak = Vec.get atoms k in
          if not (ak.neg.is_true) then begin
          (* Watcher Trouve: mettre a jour et sortir *)
            Vec.set atoms 1 ak;
            Vec.set atoms k a.neg;
            Vec.push ak.neg.watched c;
            raise Exit
          end
        done;
          (* Watcher NON Trouve *)
          if first.neg.is_true then begin
            (* la clause est fausse *)
            env.qhead <- Vec.size env.trail;
            for k = i to Vec.size watched - 1 do
              Vec.set watched !new_sz (Vec.get watched k);
              incr new_sz;
            done;
            if Options.profiling() then Profiling.bcp_conflict true true;
            raise (Conflict c)
          end
          else begin
            (* la clause est unitaire *)
            Vec.set watched !new_sz c;
            incr new_sz;
            let mlvl = best_propagation_level env c in
            enqueue env first mlvl (Some c);
            if Options.profiling() then Profiling.red true;
          end
      with Exit -> ()

  let propagate_atom env a res =
    let watched = a.watched in
    let new_sz_w = ref 0 in
    begin
      try
        for i = 0 to Vec.size watched - 1 do
          let c = Vec.get watched i in
          if not c.removed then propagate_in_clause env a c i watched new_sz_w
        done;
      with Conflict c -> assert (!res == C_none); res := C_bool c
    end;
    let dead_part = Vec.size watched - !new_sz_w in
    Vec.shrink watched dead_part true


  let do_case_split env origin =
    if Options.case_split_policy () != Util.AfterTheoryAssume then
      failwith
        "Only AfterTheoryAssume case-split policy is supported by satML";
    if Options.case_split_policy () == origin then
      try
        let tenv, _ = Th.do_case_split env.tenv in
        env.tenv <- tenv;
        C_none
      with Exception.Inconsistent (expl, classes) ->
        C_theory expl
    else C_none

  module SA =
    Set.Make
      (struct
        type t = Atom.atom
        let compare a b =
          let c = a.var.level - b.var.level in
          if c <> 0 then c
          else Atom.cmp_atom a b
      end)

  let get_atom_or_proxy f proxies =
    let open FF in
    match view f with
    | UNIT a -> a
    | _ ->
      match get_proxy_of f proxies with
      | Some a -> a
      | None -> assert false


let add_form_to_lazy_cnf =
  let open FF in
  let add_disj env ma f_a l =
    List.fold_left
      (fun ma fchild ->
        let child = get_atom_or_proxy fchild env.proxies in
        let ctt = try Matoms.find child ma |> fst with Not_found -> MFF.empty in
        Matoms.add child (MFF.add f_a l ctt, fchild) ma
      )ma l
  in
  let rec add_aux env ma (f_a : t) =
    if SFF.mem f_a env.relevants then ma
    else
      begin
        env.relevants <- SFF.add f_a env.relevants;
        match view f_a with
        | UNIT a ->
          Queue.push a env.th_tableaux;
          ma

        | AND l ->
          List.fold_left (add_aux env) ma l

        | OR l  ->
          match Lists.find_opt (fun e ->
            let p = get_atom_or_proxy e env.proxies in
            p.is_true) l
          with
          | None   -> add_disj env ma f_a l
          | Some e -> add_aux env ma e
      end
  in
  fun env ma f_a -> add_aux env ma f_a


let relevancy_propagation env ma a =
  try
    let parents, f_a = Matoms.find a ma in
    let ma = Matoms.remove a ma in
    let ma =
      MFF.fold
        (fun fp lp ma ->
          List.fold_left
            (fun ma bf ->
              let b = get_atom_or_proxy bf env.proxies in
              if eq_atom a b then ma
              else
                let mf_b, fb =
                  try Matoms.find b ma with Not_found -> assert false in
                assert (FF.equal bf fb);
                let mf_b = MFF.remove fp mf_b in
                if MFF.is_empty mf_b then Matoms.remove b ma
                else Matoms.add b (mf_b, fb) ma
            )ma lp
        )parents ma
    in
    assert (let a = get_atom_or_proxy f_a env.proxies in a.is_true);
    add_form_to_lazy_cnf env ma f_a
  with Not_found -> ma


let compute_facts_for_theory_propagate env =
  (*let a = SFF.cardinal env.relevants in*)
  env.lazy_cnf <-
    Queue.fold (relevancy_propagation env) env.lazy_cnf env.tatoms_queue;
  if Options.enable_assertions() then (*debug *)
    Matoms.iter (fun a _ -> assert (not a.is_true)) env.lazy_cnf


  let expensive_theory_propagate () = None
(* try *)
(*   if D1.d then eprintf "expensive_theory_propagate@."; *)
(*   ignore(Th.expensive_processing env.tenv); *)
(*   if D1.d then eprintf "expensive_theory_propagate => None@."; *)
(*   None *)
(* with Exception.Inconsistent dep ->  *)
(*   if D1.d then eprintf "expensive_theory_propagate => Inconsistent@."; *)
(*   Some dep *)

  let unit_theory_propagate env full_q lazy_q =
    let facts =
      Queue.fold
        (fun acc ta ->
          assert (ta.is_true);
          assert (ta.var.level >= 0);
          if ta.var.level = 0 then
            (ta.lit, Ex.empty, 0, env.cpt_current_propagations) :: acc
          else acc
        )[] lazy_q
    in
    if facts == [] then C_none
    else
      try
        (*let full_model = nb_assigns() = env.nb_init_vars in*)
        (* XXX what to do with the other results of Th.assume ? *)
        let t,_,cpt =
          Th.assume ~ordered:false
            (List.rev facts) env.unit_tenv
        in
        steps := Int64.add (Int64.of_int cpt) !steps;
        if steps_bound () <> -1
	  && Int64.compare !steps (Int64.of_int (steps_bound ())) > 0 then
	  begin
	    printf "Steps limit reached: %Ld@." !steps;
	    exit 1
	  end;
        env.unit_tenv <- t;
        C_none
      with Exception.Inconsistent (dep, terms) ->
        (* XXX what to do with terms ? *)
	(* eprintf "th inconsistent : %a @." Ex.print dep; *)
        if Options.profiling() then Profiling.theory_conflict();
        C_theory dep

  let theory_propagate env =
    let facts = ref [] in
    let dlvl = decision_level env in
    let tatoms_queue =
      if Options.tableaux_cdcl () then begin
        compute_facts_for_theory_propagate env;
        env.th_tableaux
      end
      else env.tatoms_queue
    in
    match unit_theory_propagate env env.tatoms_queue tatoms_queue with
    | C_theory dep as res -> res
    | C_bool _ -> assert false
    | C_none ->
    while not (Queue.is_empty tatoms_queue) do
      let a = Queue.pop tatoms_queue in
      let ta =
        if a.is_true then a
        else if a.neg.is_true then a.neg (* TODO: useful ?? *)
        else assert false
      in
      let ex =
        if proof () || ta.var.level > 0 then Ex.singleton (Ex.Literal ta)
        else Ex.empty
      in
      assert (Literal.LT.is_ground ta.lit);
      if ta.timp then
        ()
          [@ocaml.ppwarning "XXX: only do this for instantiation ?"]
      else
        facts := (ta.lit, ex, dlvl,env.cpt_current_propagations) :: !facts;
      env.cpt_current_propagations <- env.cpt_current_propagations + 1
    done;
    Queue.clear env.tatoms_queue;
    Queue.clear env.th_tableaux;
    if !facts == [] then C_none
    else
      try
        (*let full_model = nb_assigns() = env.nb_init_vars in*)
        (* XXX what to do with the other results of Th.assume ? *)
        let t,_,cpt =
          Th.assume ~ordered:(not (Options.tableaux_cdcl ()))
            (List.rev !facts) env.tenv
        in
        steps := Int64.add (Int64.of_int cpt) !steps;
        if steps_bound () <> -1
	  && Int64.compare !steps (Int64.of_int (steps_bound ())) > 0 then
	  begin
	    printf "Steps limit reached: %Ld@." !steps;
	    exit 1
	  end;
        env.tenv <- t;
        do_case_split env Util.AfterTheoryAssume
      (*if full_model then expensive_theory_propagate ()
        else None*)
      with Exception.Inconsistent (dep, terms) ->
        (* XXX what to do with terms ? *)
	(* eprintf "th inconsistent : %a @." Ex.print dep; *)
        if Options.profiling() then Profiling.theory_conflict();
        C_theory dep

  let propagate env =
    let num_props = ref 0 in
    let res = ref C_none in
    (*assert (Queue.is_empty env.tqueue);*)
    while env.qhead < Vec.size env.trail do
      let a = Vec.get env.trail env.qhead in
      env.qhead <- env.qhead + 1;
      incr num_props;
      propagate_atom env a res;
      Queue.push a env.tatoms_queue;
    done;
    env.propagations <- env.propagations + !num_props;
    env.simpDB_props <- env.simpDB_props - !num_props;
    !res

  let f_sort_db c1 c2 =
    let sz1 = Vec.size c1.atoms in
    let sz2 = Vec.size c2.atoms in
    let c = Pervasives.compare c1.activity c2.activity in
    if sz1 = sz2 && c = 0 then 0
    else
      if sz1 > 2 && (sz2 = 2 || c < 0) then -1
      else 1

  let locked c = false(*
                        try
                        for i = 0 to Vec.size env.vars - 1 do
                        match (Vec.get env.vars i).reason with
	                | Some c' when c ==c' -> raise Exit
	                | _ -> ()
                        done;
                        false
                        with Exit -> true*)

  let reduce_db () = ()
(*
  let extra_lim = env.clause_inc /. (to_float (Vec.size env.learnts)) in
  Vec.sort env.learnts f_sort_db;
  let lim2 = Vec.size env.learnts in
  let lim1 = lim2 / 2 in
  let j = ref 0 in
  for i = 0 to lim1 - 1 do
  let c = Vec.get env.learnts i in
  if Vec.size c.atoms > 2 && not (locked c) then
  remove_clause c
  else
  begin Vec.set env.learnts !j c; incr j end
  done;
  for i = lim1 to lim2 - 1 do
  let c = Vec.get env.learnts i in
  if Vec.size c.atoms > 2 && not (locked c) && c.activity < extra_lim then
  remove_clause c
  else
  begin Vec.set env.learnts !j c; incr j end
  done;
  Vec.shrink env.learnts (lim2 - !j) true
*)

  let remove_satisfied env vec =
    let j = ref 0 in
    let k = Vec.size vec - 1 in
    for i = 0 to k do
      let c = Vec.get vec i in
      if satisfied c then remove_clause env c
      else begin
        Vec.set vec !j (Vec.get vec i);
        incr j
      end
    done;
    Vec.shrink vec (k + 1 - !j) true


  module HUC = Hashtbl.Make
    (struct type t = clause let equal = (==) let hash = Hashtbl.hash end)


  let report_b_unsat env linit =
    if not (Options.proof ()) then begin
      env.is_unsat <- true;
      env.unsat_core <- None;
      raise (Unsat None)
    end
    else
      match linit with
      | [] | _::_::_ ->
        (* currently, report_b_unsat called with a singleton if proof = true *)
        assert false

      | [{atoms=atoms}] ->
        assert (Options.proof ());
        let l = ref linit in
        for i = 0 to Vec.size atoms - 1 do
          let v = (Vec.get atoms i).var in
          l := List.rev_append v.vpremise !l;
          match v.reason with None -> () | Some c -> l := c :: !l
        done;
        if false then begin
          eprintf "@.>>UNSAT Deduction made from:@.";
          List.iter
            (fun hc ->
              eprintf "    %a@." Atom.pr_clause hc
            )!l;
        end;
        let uc = HUC.create 17 in
        let rec roots todo =
          match todo with
          | [] -> ()
          | c::r ->
	    for i = 0 to Vec.size c.atoms - 1 do
	      let v = (Vec.get c.atoms i).var in
	      if not v.seen then begin
	        v.seen <- true;
	        roots v.vpremise;
	        match v.reason with None -> () | Some r -> roots [r];
	      end
	    done;
            match c.cpremise with
            | []    -> if not (HUC.mem uc c) then HUC.add uc c (); roots r
            | prems -> roots prems; roots r
        in roots !l;
        let unsat_core = HUC.fold (fun c _ l -> c :: l) uc [] in
        if false then begin
          eprintf "@.>>UNSAT_CORE:@.";
          List.iter
            (fun hc ->
              eprintf "    %a@." Atom.pr_clause hc
            )unsat_core;
        end;
        env.is_unsat <- true;
        let unsat_core = Some unsat_core in
        env.unsat_core <- unsat_core;
        raise (Unsat unsat_core)


  let report_t_unsat env dep =
    if not (Options.proof ()) then begin
      env.is_unsat <- true;
      env.unsat_core <- None;
      raise (Unsat None)
    end
    else
      let l =
        Ex.fold_atoms
          (fun ex l ->
            match ex with
            | Ex.Literal {var=v} ->
              let l = List.rev_append v.vpremise l in
              begin match v.reason with
              | None -> l
              | Some c -> c :: l
              end
            | _ -> assert false (* TODO *)
          ) dep []
      in
      if false then begin
        eprintf "@.>>T-UNSAT Deduction made from:@.";
        List.iter
          (fun hc ->
            eprintf "    %a@." Atom.pr_clause hc
          )l;
      end;
      let uc = HUC.create 17 in
      let rec roots todo =
        match todo with
        | [] -> ()
        | c::r ->
	  for i = 0 to Vec.size c.atoms - 1 do
	    let v = (Vec.get c.atoms i).var in
	    if not v.seen then begin
	      v.seen <- true;
	      roots v.vpremise;
	      match v.reason with None -> () | Some r -> roots [r];
	    end
	  done;
          match c.cpremise with
          | []    -> if not (HUC.mem uc c) then HUC.add uc c (); roots r
          | prems -> roots prems; roots r
      in roots l;
      let unsat_core = HUC.fold (fun c _ l -> c :: l) uc [] in
      if false then begin
        eprintf "@.>>T-UNSAT_CORE:@.";
        List.iter
          (fun hc ->
            eprintf "    %a@." Atom.pr_clause hc
          ) unsat_core;
      end;
      env.is_unsat <- true;
      let unsat_core = Some unsat_core in
      env.unsat_core <- unsat_core;
      raise (Unsat unsat_core)

(*** experimental: taken from ctrl-ergo-2 ********************

     let rec theory_simplify () =
     let theory_simplification = 2 in
     let assume a =
     assert (Literal.LT.is_ground ta.lit);
     ignore (Th.assume a.lit Ex.empty env.tenv)
     in
     if theory_simplification >= 2 then begin
     for i = 0 to Vec.size env.vars - 1 do
     try
     let a = (Vec.get env.vars i).pa in
     if not (a.is_true || a.neg.is_true) then
     try
     assume a;
     try assume a.neg
     with Exception.Inconsistent _ ->
     if debug () then
     eprintf "%a propagated m/theory at level 0@.@." Atom.pr_atom a;
     enqueue a 0 None (* Mettre Some dep pour les unsat-core*)
     with Exception.Inconsistent _ ->
     if debug () then
     eprintf "%a propagated m/theory at level 0@.@." Atom.pr_atom a.neg;
     enqueue a.neg 0 None (* Mettre Some dep pour les unsat-core*)
     with Not_found -> ()
     done;

     let head = env.qhead in
     if propagate () <> None || theory_propagate () <> None then
        raise (Unsat []);
     let head' = env.qhead in
     if head' > head then theory_simplify ()
     end
*)

  let all_propagations env =
    match propagate env with
    | C_bool c -> C_bool c
    | C_theory _ -> assert false
    | C_none ->
      match theory_propagate env with
      | C_bool _ -> assert false
      | C_theory dep -> C_theory dep
      | C_none -> C_none

  let report_conflict env c =
    match c with
    | C_bool confl -> report_b_unsat env [confl]
    | C_theory dep -> report_t_unsat env dep
    | C_none -> ()

  let simplify env =
    assert (decision_level env = 0);
    if env.is_unsat then raise (Unsat env.unsat_core);
    (* report possible propagation conflict *)
    report_conflict env (all_propagations env);
    if nb_assigns env <> env.simpDB_assigns && env.simpDB_props <= 0 then begin
      if debug () then fprintf fmt "simplify@.";
    (*theory_simplify ();*)
      if Vec.size env.learnts > 0 then remove_satisfied env env.learnts;
      if env.remove_satisfied then remove_satisfied env env.clauses;
    (*Iheap.filter env.order f_filter f_weight;*)
      env.simpDB_assigns <- nb_assigns env;
      env.simpDB_props <- env.clauses_literals + env.learnts_literals;
    end


  let record_learnt_clause env ~is_T_learn blevel learnt history size =
    let curr_level = decision_level env in
    if not is_T_learn || Options.minimal_bj () ||
       blevel = curr_level then begin
      check_levels blevel curr_level;
      match learnt with
      | [] -> assert false
      | [fuip] ->
        fuip.var.vpremise <- history;
        enqueue env fuip 0 None
      | fuip :: _ ->
        let name = fresh_lname () in
        let lclause = make_clause name learnt vraie_form size true history in
        Vec.push env.learnts lclause;
        attach_clause env lclause;
        clause_bump_activity env lclause;
        let propag_lvl = best_propagation_level env lclause in
        enqueue env fuip propag_lvl (Some lclause)
    end;
    if not is_T_learn then begin
      var_decay_activity env;
      clause_decay_activity env
    end

  let conflict_analyze_aux env c_clause max_lvl =
    let pathC = ref 0 in
    let learnt = ref SA.empty in
    let cond = ref true in
    let blevel = ref 0 in
    let seen = ref [] in
    let c = ref c_clause in
    let tr_ind = ref (Vec.size env.trail -1) in
    let history = ref [] in
    while !cond do
      if !c.learnt then clause_bump_activity env !c;
      history := !c :: !history;
      Vec.iter !c.atoms (fun a ->
          assert (a.is_true || a.neg.is_true && a.var.level >= 0);
          if not a.var.seen && a.var.level > 0 then begin
            var_bump_activity env a.var;
            a.var.seen <- true;
            seen := a :: !seen;
            if a.var.level >= max_lvl then incr pathC
            else begin
              learnt := SA.add a !learnt;
              blevel := max !blevel a.var.level
            end
          end
      );

      while assert (!tr_ind >= 0);
        let v = (Vec.get env.trail !tr_ind).var in
        not v.seen || ((Options.minimal_bj ()) && v.level < max_lvl) do
        decr tr_ind
      done;

      decr pathC;
      let p = Vec.get env.trail !tr_ind in
      decr tr_ind;
      match !pathC,p.var.reason with
      | 0, _ ->
        cond := false;
        learnt := SA.add p.neg !learnt
      | n, None -> assert false
      | n, Some cl -> c := cl
    done;
    List.iter (fun q -> q.var.seen <- false) !seen;
    let learnt = SA.elements !learnt in
    let learnt = List.fast_sort (fun a b -> b.var.level - a.var.level) learnt in
    let size = List.length learnt in
    let bj_level =
      if Options.minimal_bj () then
        match learnt with
          [] -> 0
        | a :: _ -> max 0 (a.var.level - 1)
      else !blevel
    in
    bj_level, learnt, !history, size

  let fixable_with_simple_backjump confl max_lvl lv =
    if not (Options.minimal_bj ()) then None
    else
      try
        let max_v = ref None in
        let snd_max = ref (-1) in
        List.iter
          (fun v ->
            let lvl = v.level in
            if lvl == max_lvl then begin
              if !max_v != None then raise Exit;
              max_v := Some v
            end
            else begin
              assert (lvl < max_lvl);
              snd_max := max !snd_max lvl
            end
          )lv;
        match !max_v with
        | None -> assert false
        | Some v ->
          let snd_max = !snd_max in
          assert (snd_max >= 0);
          assert (snd_max < max_lvl);
          assert (not confl.removed); (* do something otherwise ?*)
          let a = if v.pa.is_true then v.na else v.pa in
          assert (a.neg.is_true);
          assert (max_lvl > 0);
          Some (a, max_lvl - 1, snd_max)
      with Exit -> None

  let conflict_analyze_and_fix env confl =
    match confl with
    | C_none -> assert false
    | C_theory dep ->
      let atoms, sz, max_lvl, c_hist =
        Ex.fold_atoms
          (fun ex (acc, sz, max_lvl, c_hist) ->
             match ex with
             | Ex.Literal a ->
	       let c_hist = List.rev_append a.var.vpremise c_hist in
	       let c_hist = match a.var.reason with
	         | None -> c_hist | Some r -> r:: c_hist
               in
	       if a.var.level = 0 then acc, sz, max_lvl, c_hist
	       else a.neg :: acc, sz + 1, max max_lvl a.var.level, c_hist
             | _ -> assert false (* TODO *)
          ) dep ([], 0, 0, [])
      in
      if atoms == [] || max_lvl == 0 then begin
        (* check_inconsistence_of dep; *)
        report_t_unsat env dep
        (* une conjonction de faits unitaires etaient deja unsat *)
      end;
      let name = fresh_dname() in
      let c = make_clause name atoms vraie_form sz false c_hist in
      c.removed <- true;
      let blevel, learnt, history, size = conflict_analyze_aux env c max_lvl in
      cancel_until env blevel;
      record_learnt_clause env ~is_T_learn:false blevel learnt history size

    | C_bool c ->
      let max_lvl = ref 0 in
      let lv = ref [] in
      Vec.iter c.atoms (fun a ->
        max_lvl := max !max_lvl a.var.level;
        lv := a.var :: !lv
      );
      if !max_lvl == 0 then report_b_unsat env [c];
      match fixable_with_simple_backjump c !max_lvl !lv with
      | None  ->
        let blevel, learnt, history, size =
          conflict_analyze_aux env c !max_lvl in
        cancel_until env blevel;
        record_learnt_clause env ~is_T_learn:false blevel learnt history size
      | Some (a, blevel, propag_lvl) ->
        assert (a.neg.is_true);
        cancel_until env blevel;
        assert (not a.neg.is_true);
        assert (propag_lvl >= 0 && propag_lvl <= blevel);
        enqueue env a propag_lvl (Some c)


  let check_inconsistence_of dep = ()
(*
  try
  let env = ref (Th.empty()) in ();
  Ex.iter_atoms
  (fun atom ->
  let t,_,_ = Th.assume ~cs:true atom.lit (Ex.singleton atom) !env in
  env := t)
  dep;
(* ignore (Th.expensive_processing !env); *)
  assert false
  with Exception.Inconsistent _ -> ()
*)

  let rec propagate_and_stabilize env propagator conflictC =
    match propagator env with
    | C_none -> ()
    | (C_bool _ | C_theory _ ) as confl -> (* Conflict *)
      incr conflictC;
      env.conflicts <- env.conflicts + 1;
      if decision_level env = 0 then report_conflict env confl;
      conflict_analyze_and_fix env confl;
      propagate_and_stabilize env propagator conflictC

  let clause_of_dep d fuip =
    let cpt = ref 0 in
    let l =
      Ex.fold_atoms
        (fun e acc ->
          match e with
          | Ex.Literal a ->
            incr cpt;
            a.neg :: acc
          | _ -> assert false
        )d []
    in
    fuip :: l, !cpt + 1

  let th_entailed tenv a =
    if Options.no_tcp () || not (Options.minimal_bj ()) then None
    else
      let lit = Atom.literal a in
      match Th.query lit tenv with
      | Sig.Yes (d,_) ->
        a.timp <- true;
        Some (clause_of_dep d a)
      | Sig.No  ->
        match Th.query (A.neg lit) tenv with
        | Sig.Yes (d,_) ->
          a.neg.timp <- true;
          Some (clause_of_dep d a.Atom.neg)
        | Sig.No -> None

  let search env n_of_conflicts n_of_learnts =
    let conflictC = ref 0 in
    env.starts <- env.starts + 1;
    while true do
      propagate_and_stabilize env all_propagations conflictC;

      if nb_assigns env = env.nb_init_vars ||
        (Options.tableaux_cdcl () && Matoms.is_empty env.lazy_cnf) then
        raise Sat;
      if Options.enable_restarts ()
        && n_of_conflicts >= 0 && !conflictC >= n_of_conflicts then begin
          env.progress_estimate <- progress_estimate env;
          cancel_until env 0;
          raise Restart
        end;
      if decision_level env = 0 then simplify env;

      if n_of_learnts >= 0 &&
        Vec.size env.learnts - nb_assigns env >= n_of_learnts then
        reduce_db();

      let next = pick_branch_lit env in
      match th_entailed env.tenv next with
      | None ->
        new_decision_level env;
        let current_level = decision_level env in
        env.cpt_current_propagations <- 0;
        assert (next.var.level < 0);
        (* eprintf "decide: %a@." Atom.pr_atom next; *)
        enqueue env next current_level None
      | Some(c,sz) ->
        record_learnt_clause env ~is_T_learn:true (decision_level env) c [] sz
        (* right decision level will be set inside record_learnt_clause *)
    done

  let check_clause c =
    let b = ref false in
    let atoms = c.atoms in
    for i = 0 to Vec.size atoms - 1 do
      let a = Vec.get atoms i in
      b := !b || a.is_true
    done;
    assert (!b)

  let check_vec vec =
    for i = 0 to Vec.size vec - 1 do check_clause (Vec.get vec i) done

  let check_model env =
    check_vec env.clauses;
    check_vec env.learnts


  let solve env =
    if env.is_unsat then raise (Unsat env.unsat_core);
    let n_of_conflicts = ref (to_float env.restart_first) in
    let n_of_learnts =
      ref ((to_float (nb_clauses env)) *. env.learntsize_factor) in
    try
      while true do
        (try search env (to_int !n_of_conflicts) (to_int !n_of_learnts);
         with Restart -> ());
        n_of_conflicts := !n_of_conflicts *. env.restart_inc;
        n_of_learnts   := !n_of_learnts *. env.learntsize_inc;
      done;
    with
      | Sat ->
        (*check_model ();*)
        remove_satisfied env env.clauses;
        remove_satisfied env env.learnts;
        raise Sat
      | (Unsat cl) as e ->
        (* check_unsat_core cl; *)
        raise e

  exception Trivial

  let partition atoms init =
    let rec partition_aux trues unassigned falses init = function
      | [] -> trues @ unassigned @ falses, init
      | a::r ->
        if a.is_true then
	  if a.var.level = 0 then raise Trivial
	  else (a::trues) @ unassigned @ falses @ r, init
        else if a.neg.is_true then
	  if a.var.level = 0 then
	    partition_aux trues unassigned falses
	      (List.rev_append (a.var.vpremise) init) r
	  else partition_aux trues unassigned (a::falses) init r
        else partition_aux trues (a::unassigned) falses init r
    in
    partition_aux [] [] [] init atoms


  let add_clause env f ~cnumber atoms =
    if env.is_unsat then raise (Unsat env.unsat_core);
    (*if not (clause_exists atoms) then XXX TODO *)
    let init_name = string_of_int cnumber in
    let init0 =
      if Options.proof () then
        [make_clause init_name atoms f (List.length atoms) false []]
      else
        [] (* no deps if proofs generation is not enabled *)
    in
    try
      let atoms, init =
        if decision_level env = 0 then
	  let atoms, init = List.fold_left
	    (fun (atoms, init) a ->
	      if a.is_true then raise Trivial;
	      if a.neg.is_true then begin
                if Options.profiling() then Profiling.red true;
	        atoms, (List.rev_append (a.var.vpremise) init)
              end
	      else a::atoms, init
	    ) ([], init0) atoms in
	  List.fast_sort (fun a b -> a.var.vid - b.var.vid) atoms, init
        else partition atoms init0
      in
      let size = List.length atoms in
      match atoms with
        | [] ->
          report_b_unsat env init0;

        | a::b::_ ->
          let name = fresh_name () in
          let clause = make_clause name atoms vraie_form size false init in
          attach_clause env clause;
          Vec.push env.clauses clause;
          if debug_sat () && verbose () then
            fprintf fmt "[satML] add_clause: %a@." Atom.pr_clause clause;

	  if a.neg.is_true then begin (* clause is false *)
            let lvl = List.fold_left (fun m a -> max m a.var.level) 0 atoms in
            cancel_until env lvl;
            conflict_analyze_and_fix env (C_bool clause)
          end
          else
            if not a.is_true && b.neg.is_true then begin (* clause is unit *)
              let mlvl = best_propagation_level env clause in
              enqueue env a mlvl (Some clause);
            end
              [@ocaml.ppwarning "TODO: add a heavy assert that checks \
that clauses are not redundant, watchs are well set, unit and bottom \
are detected ..."]

        | [a]   ->
          if debug_sat () && verbose () then
            fprintf fmt "[satML] add_atom: %a@." Atom.pr_atom a;
          let lvl = a.var.level in
          assert (lvl <> 0);
          begin
            if not (minimal_bj ()) then cancel_until env 0
            else if a.is_true || a.neg.is_true then cancel_until env (lvl - 1)
          end;
          a.var.vpremise <- init;
          enqueue env a 0 None;
          propagate_and_stabilize env propagate (ref 0)

    with Trivial ->
      if Options.profiling() then Profiling.elim true


  let update_lazy_cnf env ~do_bcp mff ~dec_lvl =
    if Options.tableaux_cdcl () && dec_lvl <= decision_level env then begin
      let s =
        try Util.MI.find dec_lvl env.lvl_ff
        with Not_found -> SFF.empty
      in
      let lz, s =
        MFF.fold (fun ff lz_kd (l, s) ->
          match lz_kd with
          | None ->
            assert (not (MFF.mem ff env.ff_lvl));
            assert (not (SFF.mem ff s));
            env.ff_lvl <- MFF.add ff dec_lvl env.ff_lvl;
            add_form_to_lazy_cnf env l ff, SFF.add ff s
          | Some a ->
            (* TODO for case 'Some a' *)
            assert false

        ) mff (env.lazy_cnf, s)
      in
      env.lazy_cnf <- lz;
      env.lvl_ff <- Util.MI.add dec_lvl s env.lvl_ff;
      if do_bcp then
        propagate_and_stabilize (*theory_propagate_opt*)
          env all_propagations (ref 0);
    end

  let new_vars env ~nbv new_v unit_cnf nunit_cnf  =
    match new_v with
    | [] -> unit_cnf, nunit_cnf
    | _ ->
      let tenv0 = env.unit_tenv in
      Vec.grow_to_by_double env.vars nbv;
      Iheap.grow_to_by_double env.order nbv;
      let accu =
        List.fold_left
          (fun ((unit_cnf, nunit_cnf) as accu) v ->
            Vec.set env.vars v.vid v;
            insert_var_order env v;
            match th_entailed tenv0 v.pa with
            | None -> accu
            | Some (c, sz) ->
              assert (sz >= 1);
              if sz = 1 then c :: unit_cnf, nunit_cnf
              else unit_cnf, c :: nunit_cnf
                [@ocaml.ppwarning
                  "Issue: BAD decision_level, in particular, \
                   if minimal-bj is ON"]
          ) (unit_cnf, nunit_cnf) new_v
      in
      env.nb_init_vars <- nbv;
      Vec.grow_to_by_double env.model nbv;
      accu

  let set_new_proxies env proxies =
    env.proxies <- proxies

  let try_to_backjump_further =
    let rec better_bj env mf =
      let old_dlvl = decision_level env in
      let old_lazy = env.lazy_cnf in
      let old_relevants = env.relevants in
      let old_tenv = env.tenv in
      let fictive_lazy =
        MFF.fold (fun ff _ acc -> add_form_to_lazy_cnf env acc ff)
          mf old_lazy
      in
      env.lazy_cnf <- fictive_lazy;
      propagate_and_stabilize env all_propagations (ref 0);
      let new_dlvl = decision_level env in
      if old_dlvl > new_dlvl then better_bj env mf
      else
        begin
          assert (old_dlvl == new_dlvl);
          env.lazy_cnf <- old_lazy;
          env.relevants <- old_relevants;
          env.tenv     <- old_tenv
        end
    in
    fun env mff -> if Options.tableaux_cdcl () then better_bj env mff


  let assume env unit_cnf nunit_cnf f ~cnumber mff ~dec_lvl =
    begin
      match unit_cnf, nunit_cnf with
      | [], [] -> ()
      | _, _ ->
        let nbc =
          env.nb_init_clauses + List.length unit_cnf + List.length nunit_cnf in
        Vec.grow_to_by_double env.clauses nbc;
        Vec.grow_to_by_double env.learnts nbc;
        env.nb_init_clauses <- nbc;

        List.iter (add_clause env f ~cnumber) unit_cnf;
        List.iter (add_clause env f ~cnumber) nunit_cnf;

        if verbose () then  begin
          fprintf fmt "%d clauses@." (Vec.size env.clauses);
          fprintf fmt "%d learnts@." (Vec.size env.learnts);
        end
    end;
    (* do it after add clause and before T-propagate, disable bcp*)
    update_lazy_cnf env ~do_bcp:false mff ~dec_lvl;
    propagate_and_stabilize env all_propagations (ref 0); (* do bcp globally *)
    if dec_lvl > decision_level env then
      (*dec_lvl <> 0 and a bj have been made*)
      try_to_backjump_further env mff

  let exists_in_lazy_cnf env f' =
    not (Options.tableaux_cdcl ()) || MFF.mem f' env.ff_lvl

  let boolean_model env =
    let l = ref [] in
    for i = Vec.size env.trail - 1 downto 0 do
      l := (Vec.get env.trail i) :: !l
    done;
    !l

  let theory_assumed env = Th.get_assumed env.tenv

  let current_tbox env = env.tenv
  let set_current_tbox env tb = env.tenv <- tb

  let assume_th_elt env th_elt =
    assert (decision_level env == 0);
    env.tenv <- Th.assume_th_elt (current_tbox env) th_elt

  (*
  let copy (v : 'a) : 'a = Marshal.from_string (Marshal.to_string v []) 0

  let save env =
    let sv =
      { env = env;
        st_cpt_mk_var = !Solver_types.cpt_mk_var;
        st_ma = !Solver_types.ma }
    in
    copy sv
*)

  let known_lazy_formulas env = env.ff_lvl
(*end*)
end
