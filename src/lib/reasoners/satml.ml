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

(** This module implements a CDCL solver, as well as some extensions based on a
    combination of CDCL with ideas from Tableaux solver (the solver using
    Tableaux extensions is called CDCL-Tableaux).

    The CDCL part of the solver is heavily inspired by the MiniSat design:
    http://www.decision-procedures.org/handouts/MiniSat.pdf

    The Tableaux extensions to the CDCL solver mostly relate to the integration
    of a lazy CNF conversion into the CDCL solver (part of this happens in the
    [Satml_types] module).  It is described in chapter 4 of Albin Coquereau's
    PhD thesis (in French):
    https://pastel.hal.science/tel-02504894

    The lazy CNF is used in two ways:

    - With the [get_cdcl_tableaux_inst ()] option, only atoms that are relevant
       to the current state of the lazy CNF conversion are used for
       instantiation. For instance, if the formula [a \/ (b /\ c)] has been
       asserted, and we picked the left branch (i.e. [a]) in the formula, then
       only the terms in [a] will be used for instantiation -- not the terms in
       [b] or [c], even if they are decided to be [true] by the CDCL solver. Of
       course, if [b] or [c] also appear in other formulas where they have been
       "chosen", then they will be used for instantiation.contents.

       In addition, there is an early stopping mechanism for satisfiable
       problems: if all disjunctions have had one "side" successfully assigned
       to [true], the solver will not try to assign truth values to the
       remaining atoms ([b] and [c] in the example). This can lead to partial
       boolean models.

    - With the [get_cdcl_tableaux_th ()] option, atoms are only propagated to
       the theories once they become relevant. For instance, in the above
       scenario, only [a] (if it is a literal) will be propagated to the theory,
       even if [b] or [c] are later asserted (again, unless they appear in other
       formulas). *)

module E = Expr
module Atom = Satml_types.Atom
module FF = Satml_types.Flat_Formula

module Ex = Explanation

let src = Logs.Src.create ~doc:"Sat" __MODULE__
module Log = (val Logs.src_log src : Logs.LOG)

exception Sat
exception Unsat of Atom.clause list option
exception Last_UIP_reason of Atom.Set.t
exception Restart
exception Stopped

type conflict_origin =
  | C_none
  | C_bool of Atom.clause
  | C_theory of Ex.t

(* not even the final one *)
let vraie_form = E.vrai


module type SAT_ML = sig
  (*module Make (Dummy : sig end) : sig*)
  type th
  type t

  val solve : t -> unit
  val compute_concrete_model :
    declared_ids:ModelMap.profile list ->
    t ->
    Models.t Lazy.t * Objective.Model.t

  val set_new_proxies : t -> FF.proxies -> unit

  val new_vars :
    t ->
    nbv : int -> (* nb made vars *)
    Atom.var list ->
    Atom.atom list list -> Atom.atom list list ->
    Atom.atom list list * Atom.atom list list

  val assume :
    t ->
    Atom.atom list list -> Atom.atom list list -> E.t ->
    cnumber : int ->
    FF.Set.t -> dec_lvl:int ->
    unit

  val boolean_model : t -> Atom.atom list
  val instantiation_context :
    t -> FF.hcons_env -> Satml_types.Atom.Set.t
  val current_tbox : t -> th
  val set_current_tbox : t -> th -> unit
  val create : Atom.hcons_env -> t

  val assume_th_elt : t -> Expr.th_elt -> Explanation.t -> unit
  val decision_level : t -> int
  val cancel_until : t -> int -> unit

  val exists_in_lazy_cnf : t -> FF.t -> bool

  val known_lazy_formulas : t -> int FF.Map.t

  val reason_of_deduction: Atom.atom -> Atom.Set.t

  val assume_simple : t -> Atom.atom list list -> unit

  val do_case_split : t -> Util.case_split_policy -> conflict_origin

  val decide : t -> Atom.atom -> unit
  val conflict_analyze_and_fix : t -> conflict_origin -> unit

  val push : t -> Satml_types.Atom.atom -> unit
  val pop : t -> unit

  val optimize : t -> Objective.Function.t -> unit

end

module MFF = FF.Map
module SFF = FF.Set

module Vheap = Heap.MakeRanked(struct
    type t = Atom.var

    let index (a : t) = a.hindex

    let set_index (a : t) index = a.hindex <- index

    (* Note: comparison is flipped because we want maximum weight first and
       [Heap] is a min-heap. *)
    let compare (a : t) (b : t) = Float.compare b.weight a.weight
  end)

let is_semantic (a : Atom.atom) =
  match Shostak.Literal.view a.lit with
  | LTerm _ -> false
  | LSem _ -> true

module Make (Th : Theory.S) : SAT_ML with type th = Th.t = struct

  module Matoms = Atom.Map

  type th = Th.t

  module VH = Hashtbl.Make(struct
      type t = Atom.var

      let equal = Atom.equal_var

      let hash = Atom.hash_var
    end)

  type t =
    {
      hcons_env : Atom.hcons_env;

      (* si vrai, les contraintes sont deja fausses *)
      mutable is_unsat : bool;

      mutable unsat_core : Atom.clause list option;

      (* clauses du probleme *)
      clauses : Atom.clause Vec.t;

      (* clauses apprises *)
      learnts : Atom.clause Vec.t;

      (* valeur de l'increment pour l'activite des clauses *)
      mutable clause_inc : float;

      (* valeur de l'increment pour l'activite des variables *)
      mutable var_inc : float;

      (* un vecteur des variables du probleme *)
      vars : Atom.var Vec.t;

      (* la pile de decisions avec les faits impliques *)
      trail : Atom.atom Vec.t;

      (* une pile qui pointe vers les niveaux de decision dans trail *)
      trail_lim : int Vec.t;

      mutable nchoices : int ;
      (** Number of semantic choices (case splits) that have been made. Semantic
          literals are not counted as assignments but are still part of the
          trail; we keep track of this number to properly compute the number of
          assignments to boolean literals in [nb_assigns]. *)

      nchoices_stack : int Vec.t;
      (** Stack for [nchoices] values. *)

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
      order : Vheap.t;

      (* estimation de progressions, mis a jour par 'search()' *)
      (*       mutable progress_estimate : float; *)

      (* *)
      remove_satisfied : bool;

      (* inverse du facteur d'acitivte des variables, vaut 1/0.999 par defaut *)
      var_decay : float;

      (* inverse du facteur d'activite des clauses, vaut 1/0.95 par defaut *)
      clause_decay : float;

      (* la limite de restart initiale, vaut 100 par defaut *)
      restart_first : int;

      (* facteur de multiplication de restart limite, vaut 1.5 par defaut*)
      restart_inc : float;

      (* limite initiale du nombre de clause apprises, vaut 1/3
         des clauses originales par defaut *)
      learntsize_factor : float;

      (* multiplier learntsize_factor par cette valeur a chaque restart,
         vaut 1.1 par defaut *)
      learntsize_inc : float;

      mutable starts : int;

      mutable decisions : int;

      mutable propagations : int;

      mutable conflicts : int;

      mutable clauses_literals : int;

      mutable learnts_literals : int;

      mutable nb_init_clauses : int;

      mutable tenv : Th.t;

      mutable unit_tenv : Th.t;

      tenv_queue : Th.t Vec.t;

      tatoms_queue : Atom.atom Queue.t;
      (** Queue of atoms that have been added to the [trail] through either
          decision or boolean propagation, but have not been otherwise processed
          yet (in particular, they have not been propagated to the theory).

          In pure CDCL mode, all the atoms in [tatoms_queue] are propagated in
          the theory.

          In CDCL-Tableaux with the [get_cdcl_tableaux_th ()] option, the
          [tatoms_queue] is only used for relevancy propagation (see
          [relevancy_propagation]); instead, the [th_tableaux] field is used to
          dictate theory propagations. *)

      th_tableaux : Atom.atom Queue.t;
      (** Queue of atoms to propagate to the theory when using CDCL-Tableaux
          with the [get_cdcl_tableaux_th ()] option.

          The atoms in [th_tableaux] correspond to the asserted components of
          the [lazy_cnf] formulas. In particular, they always correspond to
          [UNIT] flat formulas that have been asserted (or selected in a
          disjunction).

          This ensures that atoms are propagated to the theory according to the
          structure of the formula. *)

      mutable cpt_current_propagations : int;

      mutable proxies : FF.proxies;
      (** Map from flat formulas to the proxies that represent them.

          Note: the [Satml] module does not touch the [proxies] field itself; it
          only uses it to find the atom associated with a flat formula.
          Appropriate proxies that cover all the flat formulas to be encountered
          need to be pre-emptively given using [set_new_proxies], which is
          called from [Satml_frontend]. *)

      mutable lazy_cnf :
        (FF.t list MFF.t * FF.t) Matoms.t;
      (** Map from atoms [a] to pairs [parents, ff].

          The [lazy_cnf] field is only used by the CDCL-Tableaux solver. It is
          used in relevancy propagation (see [relevancy_propagation]) when the
          [get_cdcl_tableaux_th ()] option is enabled, and to stop decisions as
          soon as the *relevant* parts of the assertions have been decided if
          the [get_cdcl_tableaux_inst ()] option is enabled.

          It satisfies the following invariants:

          - [ff] is the flat formula that the atom [a] represents (either
             directly if [ff] is an UNIT formula, or indirectly as a proxy -- in
             which case, [a] is the proxy associated with [ff] in [proxies]).

          - [parents] is the set of _disjunctive_ flat formulas that contain
             [ff] ([parents] is a map whose entries are always of the form
             [FF.OR l -> l], where [ff] appears in [l]).

          - The formulas in [parents] represent the disjunctions that have been
             asserted but not yet proven (i.e. none of their components is
             [true]).

          - The atoms that appear as keys in [lazy_cnf] are not [true] (they
             are either undecided or forced to [false]).  Once an atom in
             [lazy_cnf] is forced to [true], it is removed from the [lazy_cnf]
             and its parents are removed as parents of their other children (one
             of their components is [true], so they no longer constrain the
             problem). The corresponding flat formula is then added again, which
             may introduce new entries to the [lazy_cnf] if it was itself a
             disjunction or contained disjunctions (see
             [relevancy_propagation]).

          When [lazy_cnf] is empty, all the disjunctions have been decided, and
          we have a (partial!) boolean model. If there are nested disjunctions
          (for instance, if [a \/ (b /\ (c \/ d))] is asserted, and we decide or
          propagate that [a] is true, [c] and [d] may stay undecided). *)

      lazy_cnf_queue :
        (FF.t list MFF.t * FF.t) Matoms.t Vec.t;
      (** Checkpoint of the [lazy_cnf] field at each decision level. Only used
          with the CDCL-Tableaux solver. *)

      irrelevants : unit VH.t;
      (** Variables that have been removed from the set of possible decisions
          due to no longer being relevant to the original formula (i.e. they are
          undecided but also no longer in the [lazy_cnf]).

          We maintain the following invariants:

          - Any *undecided* variable is either in the [order] heap, or in the
             [irrelevants] set
          - Any variable in the [irrelevants] set is not relevant (i.e. neither
             [v.na] nor [v.pa] is in the [lazy_cnf] -- this invariant is locally
             broken inside [try_to_backjump_further], but we don't make
             decisions there, so it is fine)

          Variables from the [irrelevants] set are added back to the [order]
          heap upon backtracking if they become relevant at the backtracked
          level, otherwise they stay in the [irrelevants] set. *)

      mutable relevants : SFF.t;
      (** Set of relevant flat formulas. These are the formulas that have been
          added to the lazy CNF (i.e. asserted), including sub-formulas that are
          true.

          For instance, when asserting [a \/ (b /\ c)], the formula
          [a \/ (b /\ c)] is added to the [relevants] set; when deciding to pick
          the second branch of the disjunction, the formulas [b /\ c], [b] and
          [c] are added to the [relevants] set (see [add_form_to_lazy_cnf]).

          Used to extract relevant terms for instantiation when only option
          [get_cdcl_tableaux_inst ()] (but not [get_cdcl_tableaux_th ()]) is
          enabled. *)

      relevants_queue : SFF.t Vec.t;
      (** Checkpoint of the [relevant] field at each decision level. Only used
          with the CDCL-Tableaux solver. *)

      mutable ff_lvl : int MFF.t;
      (** Map from flat formulas to the (earliest) decision level at which they
          were asserted. Only used with the CDCL-Tableaux solver. *)

      mutable lvl_ff : SFF.t Util.MI.t;
      (** Map from decision level to the set of flat formulas asserted at that
          level. Set inverse of [ff_lvl]. Only used with the CDCL-Tableaux
          solver. *)

      increm_guards : Atom.atom Vec.t;

      mutable next_dec_guard : int;

      objectives : Objective.Function.t list Vec.t;
      (** Queue of the objectives per incremental levels.

          Notice that objectives of the incremental toplevel are
          directly added to the theory and so do not appear in this queue. *)

      mutable next_decisions : Atom.atom list;
      (** Literals that must be decided on before the solver can answer [Sat].

          These are added by the theory through calls to
          [acts_add_decision_lit]. *)

      mutable next_split : Atom.atom option;
      (** Literal that should be decided on before the solver answers [Sat].

          These are added by the theory through calls to [acts_add_split]. The
          difference with [next_decisions] is that the [splits] are optional
          (i.e. they can be dropped, and the solver is allowed to answer [Sat]
          without deciding on the splits if it chooses so) whereas once added,
          the [decisions] are guaranteed to be decided on at some point (unless
          backtracking occurs). *)

      mutable next_optimized_split :
        (Objective.Function.t * Objective.Value.t * Atom.atom) option;
      (** Objective functions that must be optimized before the solver can
          answer [Sat].

          The provided [Atom.atom] correspond to a decision forcing the
          [Function.t] to the corresponding [Value.t] (or nudging the model
          towards "more optimal" values if the objective is not reachable); once
          the decision is made by the solver, the optimized value is sent back
          to the theory through [Th.add_objective]. *)
    }

  exception Conflict of Atom.clause
  (*module Make (Dummy : sig end) = struct*)

  let create hcons_env =
    {
      hcons_env;

      is_unsat = false;

      unsat_core = None;

      clauses = Vec.make 0 ~dummy:Atom.dummy_clause;
      (*sera mis a jour lors du parsing*)

      learnts = Vec.make 0 ~dummy:Atom.dummy_clause;
      (*sera mis a jour lors du parsing*)

      clause_inc = 1.;

      var_inc = 1.;

      vars = Vec.make 0 ~dummy:Atom.dummy_var;
      (*sera mis a jour lors du parsing*)

      trail = Vec.make 601 ~dummy:Atom.dummy_atom;

      trail_lim = Vec.make 601 ~dummy:(-105);

      nchoices = 0;

      nchoices_stack = Vec.make 100 ~dummy:(-105);

      qhead = 0;

      simpDB_assigns = -1;

      simpDB_props = 0;

      order = Vheap.create 0 Atom.dummy_var; (* sera mis a jour dans solve *)

      (*       progress_estimate = 0.; *)

      remove_satisfied = true;

      var_decay = 1. /. 0.95;

      clause_decay = 1. /. 0.999;

      restart_first = 100;

      restart_inc = 1.5;

      learntsize_factor = 1. /. 3. ;

      learntsize_inc = 1.1;

      starts = 0;

      decisions = 0;

      propagations = 0;

      conflicts = 0;

      clauses_literals = 0;

      learnts_literals = 0;

      nb_init_clauses = 0;

      tenv = Th.empty();

      unit_tenv = Th.empty();

      tenv_queue = Vec.make 100 ~dummy:(Th.empty());

      tatoms_queue = Queue.create ();

      th_tableaux = Queue.create ();

      cpt_current_propagations = 0;

      proxies = FF.empty_proxies;

      lazy_cnf = Matoms.empty;

      lazy_cnf_queue =
        Vec.make 100
          ~dummy:(Matoms.singleton (Atom.faux_atom) (MFF.empty, FF.faux));

      irrelevants = VH.create 17;

      relevants = SFF.empty;
      relevants_queue = Vec.make 100 ~dummy:(SFF.singleton (FF.faux));

      ff_lvl = MFF.empty;

      lvl_ff = Util.MI.empty;

      increm_guards = Vec.make 1 ~dummy:Atom.dummy_atom;

      objectives = Vec.make 1 ~dummy:[];

      next_dec_guard = 0;

      next_decisions = [];

      next_split = None;

      next_optimized_split = None;
    }

  let insert_var_order env (v : Atom.var) =
    Vheap.insert env.order v

  let var_decay_activity env = env.var_inc <- env.var_inc *. env.var_decay

  let clause_decay_activity env =
    env.clause_inc <- env.clause_inc *. env.clause_decay

  let var_bump_activity env (v : Atom.var) =
    v.weight <- v.weight +. env.var_inc;
    if Float.compare v.weight 1e100 > 0 then begin
      Vec.iter
        (fun (v : Atom.var) ->
           v.weight <- v.weight *. 1e-100
        ) env.vars;
      env.var_inc <- env.var_inc *. 1e-100;
    end;
    if Vheap.in_heap v then
      Vheap.decrease env.order v


  let clause_bump_activity env (c : Atom.clause) =
    c.activity <- c.activity +. env.clause_inc;
    if Float.compare c.activity 1e20 > 0 then begin
      Vec.iter (fun (clause : Atom.clause) ->
          clause.activity <- clause.activity *. 1e-20
        ) env.learnts;
      env.clause_inc <- env.clause_inc *. 1e-20
    end

  let decision_level env = Vec.size env.trail_lim

  let nb_choices env = env.nchoices
  let nb_assigns env = Vec.size env.trail - nb_choices env
  let nb_clauses env = Vec.size env.clauses
  (* unused -- let nb_learnts env = Vec.size env.learnts *)
  let nb_vars    env = Vec.size env.vars

  let new_decision_level env =
    env.decisions <- env.decisions + 1;
    Vec.push env.trail_lim (Vec.size env.trail);
    Vec.push env.nchoices_stack env.nchoices;
    if Options.get_profiling() then
      Profiling.decision (decision_level env) "<none>";
    Vec.push env.tenv_queue env.tenv; (* save the current tenv *)
    if Options.get_cdcl_tableaux () then begin
      Vec.push env.lazy_cnf_queue env.lazy_cnf;
      Vec.push env.relevants_queue env.relevants
    end

  let attach_clause env (c : Atom.clause) =
    Vec.push (Vec.get c.atoms 0).neg.watched c;
    Vec.push (Vec.get c.atoms 1).neg.watched c;
    if c.learnt then
      env.learnts_literals <- env.learnts_literals + Vec.size c.atoms
    else
      env.clauses_literals <- env.clauses_literals + Vec.size c.atoms

  let detach_clause env (c : Atom.clause) =
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

  let satisfied (c : Atom.clause) =
    Vec.exists (fun (atom : Atom.atom) ->
        atom.is_true && atom.var.level == 0
      ) c.atoms

  let is_assigned (a : Atom.atom) =
    a.is_true || a.neg.is_true

  let unassign_atom (a : Atom.atom) =
    a.is_true <- false;
    a.neg.is_true <- false;
    a.timp <- 0;
    a.neg.timp <- 0;
    a.var.level <- -1;
    a.var.index <- -1;
    a.var.reason <- None;
    a.var.vpremise <- []

  let enqueue_assigned env (a : Atom.atom) =
    if Options.get_debug_sat () then
      Printer.print_dbg "[satml] enqueue_assigned: %a@." Atom.pr_atom a;
    if a.neg.is_guard then begin
      (* if the negation of a is (still) a guard, it should be forced to true
         during the first decisions.
         If the SAT tries to deduce that a.neg is true (ie. a is false),
         then we have detected an inconsistency. *)
      assert (a.var.level <= env.next_dec_guard);
      (* guards are necessarily decided/propagated before all other atoms *)
      raise (Unsat None);
    end;
    assert (a.is_true || a.neg.is_true);
    if a.timp = 1 then begin
      a.timp <- -1;
      a.neg.timp <- -1
    end;
    assert (a.var.level >= 0);
    Vec.push env.trail a;
    if is_semantic a then
      env.nchoices <- env.nchoices + 1

  let cancel_ff_lvls_until env lvl =
    for i = decision_level env downto lvl + 1 do
      try
        let s = Util.MI.find i env.lvl_ff in
        SFF.iter (fun f' -> env.ff_lvl <- MFF.remove f' env.ff_lvl) s;
        env.lvl_ff <- Util.MI.remove i env.lvl_ff;
      with Not_found -> ()
    done

  (* Variables are relevant if they are in the [lazy_cnf]. Semantic variables
     are always relevant: otherwise, since they are local to the current branch
     and not added to the [var_order], they would never get decided.

     Only used when [Options.get_cdcl_tableaux_inst ()] is enabled. *)
  let is_relevant env (v : Atom.var) =
    is_semantic v.pa ||
    Matoms.mem v.pa env.lazy_cnf || Matoms.mem v.na env.lazy_cnf

  (* annule tout jusqu'a lvl *exclu*  *)
  let cancel_until env lvl =
    if Options.get_debug_sat () then
      Printer.print_dbg
        "[satml] cancel until %d (current is %d)@." lvl (decision_level env);
    cancel_ff_lvls_until env lvl;
    let repush = ref [] in
    if decision_level env > lvl then begin
      env.qhead <- Vec.get env.trail_lim lvl;
      for c = Vec.size env.trail - 1 downto env.qhead do
        let a = Vec.get env.trail c in
        if Options.get_minimal_bj () && a.var.level <= lvl then begin
          assert (a.var.level = 0 || a.var.reason != None);
          repush := a :: !repush
        end
        else begin
          unassign_atom a;
          if a.is_guard then
            env.next_dec_guard <- env.next_dec_guard - 1;
          if not (is_semantic a) then
            insert_var_order env a.var
        end
      done;
      Queue.clear env.tatoms_queue;
      Queue.clear env.th_tableaux;
      env.tenv <- Vec.get env.tenv_queue lvl; (* recover the right tenv *)
      env.nchoices <- Vec.get env.nchoices_stack lvl;
      if Options.get_cdcl_tableaux () then begin
        env.lazy_cnf <- Vec.get env.lazy_cnf_queue lvl;
        env.relevants <- Vec.get env.relevants_queue lvl;
      end;
      Vec.shrink env.trail env.qhead;
      Vec.shrink env.trail_lim lvl;
      Vec.shrink env.nchoices_stack lvl;
      Vec.shrink env.tenv_queue lvl;
      if Options.get_cdcl_tableaux () then begin
        Vec.shrink
          env.lazy_cnf_queue lvl;
        Vec.shrink env.relevants_queue
          lvl
        [@ocaml.ppwarning "TODO: try to disable 'fill_with_dummy'"]
      end;
      (try
         let last_dec =
           if Vec.size env.trail_lim = 0 then 0 else Vec.last env.trail_lim in
         env.cpt_current_propagations <- (Vec.size env.trail) - last_dec
       with _ -> assert false
      );
      env.next_decisions <- [];
      env.next_split <- None;
      env.next_optimized_split <- None;
      (* Some variables that were irrelevant because of canceled
         decisions/propagations may become relevant again. Add them back to the
         heap. *)
      if Options.get_cdcl_tableaux_inst () then
        VH.filter_map_inplace (fun v () ->
            if is_relevant env v then (
              insert_var_order env v; None
            ) else
              Some ()
          ) env.irrelevants;
    end;
    if Options.get_profiling() then Profiling.reset_dlevel (decision_level env);
    assert (Vec.size env.trail_lim = Vec.size env.tenv_queue);
    assert (Vec.size env.trail_lim = Vec.size env.nchoices_stack);
    assert (Options.get_minimal_bj () || (!repush == []));
    List.iter (enqueue_assigned env) !repush

  let debug_enqueue_level a lvl reason =
    match reason with
    | None -> true
    | Some (c : Atom.clause) ->
      let maxi = ref min_int in
      Vec.iter (fun (atom : Atom.atom) ->
          if not (Atom.eq_atom a atom) then
            maxi := max !maxi atom.var.level
        ) c.atoms;
      !maxi = lvl

  let max_level_in_clause (c : Atom.clause) =
    let max_lvl = ref 0 in
    Vec.iter (fun (a : Atom.atom) ->
        max_lvl := max !max_lvl a.var.level) c.atoms;
    !max_lvl

  let enqueue env (a : Atom.atom) lvl reason =
    assert (not a.is_true && not a.neg.is_true &&
            a.var.level < 0 && a.var.reason == None && lvl >= 0);
    if a.neg.is_guard then begin
      (* if the negation of a is (still) a guard, it should be forced to true
         during the first decisions.
         If the SAT tries to deduce that a.neg is true (ie. a is false),
         then we have detected an inconsistency. *)
      assert (a.var.level <= env.next_dec_guard);
      (* guards are necessarily decided/propagated before all other atoms *)
      raise (Unsat None);
    end;
    (* Garder la reason car elle est utile pour les unsat-core *)
    (*let reason = if lvl = 0 then None else reason in*)
    a.is_true <- true;
    a.var.level <- lvl;
    a.var.reason <- reason;
    if Options.get_debug_sat () then
      Printer.print_dbg "[satml] enqueue: %a@." Atom.pr_atom a;
    Vec.push env.trail a;
    if is_semantic a then
      env.nchoices <- env.nchoices + 1;
    a.var.index <- Vec.size env.trail;
    Options.heavy_assert (fun () -> debug_enqueue_level a lvl reason)

  (* let progress_estimate env =
     let prg = ref 0. in
     let nbv = Atom.to_float (nb_vars env) in
     let lvl = decision_level env in
     let _F = 1. /. nbv in
     for i = 0 to lvl do
      let _beg = if i = 0 then 0 else Vec.get env.trail_lim (i-1) in
      let _end =
        if i=lvl then Vec.size env.trail
        else Vec.get env.trail_lim i in
      prg := !prg +. _F**(Atom.to_float i) *. (Atom.to_float (_end - _beg))
     done;
     !prg /. nbv *)

  let check_levels propag_lvl current_lvl =
    assert (propag_lvl <= current_lvl);
    assert (propag_lvl == current_lvl || (Options.get_minimal_bj ()))

  let best_propagation_level env c =
    let mlvl =
      if Options.get_minimal_bj () then max_level_in_clause c
      else decision_level env
    in
    check_levels mlvl (decision_level env);
    mlvl

  let propagate_in_clause env (a : Atom.atom) (c : Atom.clause)
      i watched new_sz =
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
      if Options.get_profiling() then Profiling.elim true;
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
          if Options.get_profiling() then Profiling.bcp_conflict true true;
          raise (Conflict c)
        end
        else begin
          (* la clause est unitaire *)
          Vec.set watched !new_sz c;
          incr new_sz;
          let mlvl = best_propagation_level env c in
          enqueue env first mlvl (Some c);
          if Options.get_profiling() then Profiling.red true;
        end
      with Exit -> ()

  let propagate_atom env (a : Atom.atom) res =
    let watched = a.watched in
    let new_sz_w = ref 0 in
    begin
      try
        Vec.iteri (fun i (clause : Atom.clause) ->
            if not clause.removed then
              propagate_in_clause env a clause i watched new_sz_w
          ) watched;
      with Conflict c -> assert (!res == C_none); res := C_bool c
    end;
    Vec.shrink watched !new_sz_w

  let acts_add_decision_lit env lit =
    let atom, _ = Atom.add_atom env.hcons_env lit [] in
    if atom.var.level < 0 then (
      assert (not atom.is_true && not atom.neg.is_true);
      env.next_decisions <- atom :: env.next_decisions
    ) else
      assert (atom.is_true || atom.neg.is_true)

  let acts_add_split env lit =
    let atom, _ = Atom.add_atom env.hcons_env lit [] in
    if atom.var.level < 0 then (
      assert (not atom.is_true && not atom.neg.is_true);
      env.next_split <- Some atom
    ) else
      assert (atom.is_true || atom.neg.is_true)

  let acts_add_objective env fn value lit =
    (* Note: we must store the objective even if the atom is already true,
       because we must send back the objective to the theory afterwards.

       We can't update the theory inside this function, because it is called
       from within the theory. *)
    let atom, _ = Atom.add_atom env.hcons_env lit [] in
    env.next_optimized_split <- Some (fn, value, atom)

  let[@inline] theory_slice env : _ Th_util.acts = {
    acts_add_decision_lit = acts_add_decision_lit env ;
    acts_add_split = acts_add_split env ;
    acts_add_objective = acts_add_objective env ;
  }

  let do_case_split env origin =
    try
      let acts = theory_slice env in
      let tenv, _terms = Th.do_case_split ~acts env.tenv origin in
      (* TODO: terms not added to matching !!! *)
      env.tenv <- tenv;
      C_none
    with Ex.Inconsistent (expl, _) ->
      C_theory expl

  module SA = Atom.Set

  let get_atom_or_proxy f proxies =
    let open FF in
    match view f with
    | UNIT a -> a
    | _ ->
      match get_proxy_of f proxies with
      | Some a -> a
      | None -> assert false


  (* [add_form_to_lazy_cnf env lazy_cnf ff] updates [env] and [lazy_cnf] by
     assuming the flat formula [ff].

     More precisely:

     - [ff] and any conjunctive component (i.e. if [ff = ff_1 /\ ff_2], [ff_1]
        and [ff_2] are conjunctive components, recursively) are added to the
        [relevant] field in [env];
     - UNIT formulas (either [ff] or in a conjunctive component) are added to
        the [th_tableaux] queue in [env] (NOTE: [th_tableaux] is only used if
        the [get_cdcl_tableaux_th ()] option is enabled);
     - Disjunctive formulas that contain a component already known to be true
        are treated as that component (this is used by [relevancy_propagation]
        which adds the decided children of disjunctive formulas -- it is also
        necessary for soundness in case a child atom was propagated earlier than
        expected e.g. due to clause learning);
     - Disjunctive formulas that are still undecided are added to the
        [lazy_cnf] (see documentation of the [lazy_cnf] field in [env]). *)
  let add_form_to_lazy_cnf =
    let open FF in
    let add_disj env ma f_a l =
      List.fold_left
        (fun ma fchild ->
           let child = get_atom_or_proxy fchild env.proxies in
           let ctt =
             try Matoms.find child ma |> fst with Not_found -> MFF.empty
           in
           (* The variable becomes relevant and is not decided: add it back to
              the heap in case it has been removed. *)
           VH.remove env.irrelevants child.var;
           insert_var_order env child.var;
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
            match List.find_opt (fun e ->
                let p = get_atom_or_proxy e env.proxies in
                p.is_true) l
            with
            | None   -> add_disj env ma f_a l
            | Some e -> add_aux env ma e
        end
    in
    fun env ma f_a -> add_aux env ma f_a


  (** [relevancy_propagation env lazy_cnf a] propagates the fact that atom [a]
      is now true to [env] and the [lazy_cnf].

      More precisely, if [a] was an atom in the [lazy_cnf] (i.e. if a formula of
      the form [a_0 \/ ... \/ a \/ ... \/ a_n] must hold given the current
      CNF unfolding), its parents are removed from the [lazy_cnf] and [a] is
      added again to the [lazy_cnf]. This will either add [a] to the
      [th_tableaux] field (if [a] corresponds to a [UNIT] flat formula that was
      asserted), or otherwise perform one step of CNF unfolding and add the
      formula that [a] was a proxy for to the [lazy_cnf] (see
      [add_form_to_lazy_cnf]). *)
  let relevancy_propagation env ma a =
    match Shostak.Literal.view @@ Atom.literal a with
    | LSem _ ->
      (* Always propagate back semantic literals to the theory. *)
      Queue.push a env.th_tableaux;
      ma

    | LTerm _ ->
      try
        let parents, f_a = Matoms.find a ma in
        let ma = Matoms.remove a ma in
        let ma =
          MFF.fold
            (fun fp lp ma ->
               List.fold_left
                 (fun ma bf ->
                    let b = get_atom_or_proxy bf env.proxies in
                    if Atom.eq_atom a b then ma
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


  (* Note: although this seems to only update [env.lazy_cnf], the call to
     [relevancy_propagation] in fact updates the [th_tableaux] queue, which is
     the one used for theory propagation when [get_cdcl_tableaux_th ()] is
     enabled.

     When only [get_cdcl_tableaux_inst ()] is enabled, we still need to call
     this, because the update of [lazy_cnf] is required for early stopping. *)
  let compute_facts_for_theory_propagate env =
    (*let a = SFF.cardinal env.relevants in*)
    env.lazy_cnf <-
      Queue.fold (relevancy_propagation env) env.lazy_cnf env.tatoms_queue;
    Options.heavy_assert (fun () ->
        Matoms.for_all (fun a _ -> not a.is_true) env.lazy_cnf
      )

  let _expensive_theory_propagate () = None
  (* try *)
  (*   if D1.d then Printer.print_dbg
       "expensive_theory_propagate@."; *)
  (*   ignore(Th.expensive_processing env.tenv); *)
  (*   if D1.d then Printer.print_dbg
          "expensive_theory_propagate => None@."; *)
  (*   None *)
  (* with Ex.Inconsistent dep ->  *)
  (*   if D1.d then Printer.print_dbg
       "expensive_theory_propagate => Inconsistent@."; *)
  (*   Some dep *)

  let unit_theory_propagate env _full_q lazy_q =
    let nb_f = ref 0 in
    let facts =
      Queue.fold
        (fun acc (ta : Atom.atom) ->
           assert (ta.is_true);
           assert (ta.var.level >= 0);
           if ta.var.level = 0 then begin
             incr nb_f;
             (ta.lit, Th_util.Other, Ex.empty, 0, env.cpt_current_propagations)
             :: acc
           end
           else acc
        )[] lazy_q
    in
    if Options.get_debug_sat () then
      Printer.print_dbg "[satml] Unit theory_propagate of %d atoms@." !nb_f;
    if facts == [] then C_none
    else
      try
        (*let full_model = nb_assigns() = nb_vars () in*)
        (* XXX what to do with the other results of Th.assume ? *)
        let t,_,cpt =
          Th.assume ~ordered:false
            (List.rev facts) env.unit_tenv
        in
        Steps.incr (Steps.Th_assumed cpt);
        env.unit_tenv <- t;
        C_none
      with Ex.Inconsistent (dep, _terms) ->
        (* XXX what to do with terms ? *)
        (* Printer.print_dbg
           "th inconsistent : %a @." Ex.print dep; *)
        if Options.get_profiling() then Profiling.theory_conflict();
        C_theory dep

  let theory_propagate env =
    let facts = ref [] in
    let dlvl = decision_level env in
    if Options.get_cdcl_tableaux () then
      compute_facts_for_theory_propagate env;
    let tatoms_queue =
      if Options.get_cdcl_tableaux_th () then begin
        env.th_tableaux
      end
      else env.tatoms_queue
    in
    match unit_theory_propagate env env.tatoms_queue tatoms_queue with
    | C_theory _ as res -> res
    | C_bool _ -> assert false
    | C_none ->
      let nb_f = ref 0 in
      while not (Queue.is_empty tatoms_queue) do
        let a = Queue.pop tatoms_queue in
        incr nb_f;
        let ta =
          if a.is_true then a
          else if a.neg.is_true then a.neg (* TODO: useful ?? *)
          else assert false
        in
        let ex =
          if Options.get_unsat_core () || ta.var.level > 0 then
            Ex.singleton (Ex.Literal ta)
          else Ex.empty
        in
        assert (Shostak.Literal.is_ground ta.lit);
        let th_imp =
          if ta.timp = -1 then
            match Shostak.Literal.view @@ Atom.literal a with
            | LSem _ -> false
            | LTerm lit ->
              match Th.query lit env.tenv with
              | Some _ ->
                a.timp <- 1;
                a.neg.timp <- 1;
                true
              | None ->
                false
          else
            ta.timp = 1
        in
        if not th_imp then
          facts :=
            (ta.lit, Th_util.Other, ex, dlvl,env.cpt_current_propagations) ::
            !facts;
        env.cpt_current_propagations <- env.cpt_current_propagations + 1
      done;
      if Options.get_debug_sat () then
        Printer.print_dbg "[satml] Theory_propagate of %d atoms@." !nb_f;
      Queue.clear env.tatoms_queue;
      Queue.clear env.th_tableaux;
      if !facts == [] then C_none
      else
        try
          (*let full_model = nb_assigns() = nb_vars () in*)
          (* XXX what to do with the other results of Th.assume ? *)
          let t,_,cpt =
            Th.assume ~ordered:(not (Options.get_cdcl_tableaux_th ()))
              (List.rev !facts) env.tenv
          in
          Steps.incr (Steps.Th_assumed cpt);
          env.tenv <- t;
          do_case_split env Util.AfterTheoryAssume
        (*if full_model then expensive_theory_propagate ()
          else None*)
        with Ex.Inconsistent (dep, _terms) ->
          (* XXX what to do with terms ? *)
          (* Printer.print_dbg
             "th inconsistent : %a @." Ex.print dep; *)
          if Options.get_profiling() then Profiling.theory_conflict();
          C_theory dep

  let propagate env =
    let num_props = ref 0 in
    let res = ref C_none in
    (*assert (Queue.is_empty env.tqueue);*)
    while env.qhead < Vec.size env.trail do
      let a = Vec.get env.trail env.qhead in
      if Options.get_debug_sat () then
        Printer.print_dbg "[satml] propagate atom %a@." Atom.pr_atom a;
      env.qhead <- env.qhead + 1;
      incr num_props;
      propagate_atom env a res;
      Queue.push a env.tatoms_queue;
    done;
    env.propagations <- env.propagations + !num_props;
    env.simpDB_props <- env.simpDB_props - !num_props;
    !res

  (* unused --
     let f_sort_db c1 c2 =
     let sz1 = Vec.size c1.atoms in
     let sz2 = Vec.size c2.atoms in
     let c = Stdlib.compare c1.activity c2.activity in
     if sz1 = sz2 && c = 0 then 0
     else
     if sz1 > 2 && (sz2 = 2 || c < 0) then -1
     else 1

     let locked _ = false
     (*
     try
      for i = 0 to Vec.size env.vars - 1 do
      match (Vec.get env.vars i).reason with
        | Some c' when c ==c' -> raise Exit
        | _ -> ()
      done;
      false
     with Exit -> true
   *)
  *)

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
  Vec.shrink env.learnts !j true
*)

  let remove_satisfied env vec =
    let j = ref 0 in
    for i = 0 to Vec.size vec - 1 do
      let c = Vec.get vec i in
      if satisfied c then remove_clause env c
      else begin
        Vec.set vec !j (Vec.get vec i);
        incr j
      end
    done;
    Vec.shrink vec !j


  module HUC = Hashtbl.Make
      (struct type t = Atom.clause let equal = (==) let hash = Hashtbl.hash end)

  let print_aux fmt hc =
    Format.fprintf fmt "%a@," Atom.pr_clause hc

  let report_b_unsat env linit =
    if not (Options.get_unsat_core ()) then begin
      env.is_unsat <- true;
      env.unsat_core <- None;
      raise (Unsat None)
    end
    else
      match linit with
      | [] | _::_::_ ->
        (* currently, report_b_unsat called with a singleton
           if get_unsat_core = true *)
        assert false

      | [{ Atom.atoms; _ }] ->
        assert (Options.get_unsat_core ());
        let l = ref linit in
        Vec.iter (fun (atom : Atom.atom) ->
            l := List.rev_append atom.var.vpremise !l;
            match atom.var.reason with None -> () | Some c -> l := c :: !l
          ) atoms;
        Printer.print_dbg ~header:false
          "@[<v 2>UNSAT Deduction made from:@ %a@]"
          (Printer.pp_list_no_space print_aux) !l;
        let uc = HUC.create 17 in
        let rec roots todo =
          match todo with
          | [] -> ()
          | (c : Atom.clause) ::r ->
            Vec.iter (fun (atom : Atom.atom) ->
                if not atom.var.seen then begin
                  atom.var.seen <- true;
                  roots atom.var.vpremise;
                  match atom.var.reason with None -> () | Some r -> roots [r]
                end
              ) c.atoms;
            match c.cpremise with
            | []    -> if not (HUC.mem uc c) then HUC.add uc c (); roots r
            | prems -> roots prems; roots r
        in roots !l;
        let unsat_core = HUC.fold (fun c _ l -> c :: l) uc [] in
        Printer.print_dbg ~header:false "@[<v 2>UNSAT_CORE:@ %a@]"
          (Printer.pp_list_no_space print_aux) unsat_core;
        env.is_unsat <- true;
        let unsat_core = Some unsat_core in
        env.unsat_core <- unsat_core;
        raise (Unsat unsat_core)


  let report_t_unsat env dep =
    if not (Options.get_unsat_core ()) then begin
      env.is_unsat <- true;
      env.unsat_core <- None;
      raise (Unsat None)
    end
    else
      let l =
        Ex.fold_atoms
          (fun ex l ->
             match ex with
             | Ex.Literal { var = v; _ } ->
               let l = List.rev_append v.vpremise l in
               begin match v.reason with
                 | None -> l
                 | Some c -> c :: l
               end
             | _ -> assert false (* TODO *)
          ) dep []
      in
      Printer.print_dbg ~header:false
        "@[<v 2>T-UNSAT Deduction made from:@ %a@]"
        (Printer.pp_list_no_space print_aux) l;
      let uc = HUC.create 17 in
      let rec roots todo =
        match todo with
        | [] -> ()
        | (c : Atom.clause) ::r ->
          Vec.iter (fun (atom : Atom.atom) ->
              if not atom.var.seen then begin
                atom.var.seen <- true;
                roots atom.var.vpremise;
                match atom.var.reason with None -> () | Some r -> roots [r]
              end
            ) c.atoms;
          match c.cpremise with
          | []    -> if not (HUC.mem uc c) then HUC.add uc c (); roots r
          | prems -> roots prems; roots r
      in roots l;
      let unsat_core = HUC.fold (fun c _ l -> c :: l) uc [] in
      Printer.print_dbg ~header:false
        "@[<v 2>T-UNSAT_CORE:@ %a@]"
        (Printer.pp_list_no_space print_aux) unsat_core;
      env.is_unsat <- true;
      let unsat_core = Some unsat_core in
      env.unsat_core <- unsat_core;
      raise (Unsat unsat_core)

  (*** experimental: taken from ctrl-ergo-2 ********************

       let rec theory_simplify () =
       let theory_simplification = 2 in
       let assume a =
       assert (E.is_ground ta.lit);
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
       with Ex.Inconsistent _ ->
       if debug () then
       Printer.print_dbg
       "%a propagated m/theory at level 0@." Atom.pr_atom a;
       enqueue a 0 None (* Mettre Some dep pour les unsat-core*)
       with Ex.Inconsistent _ ->
       if debug () then
       Printer.print_dbg
       "%a propagated m/theory at level 0@." Atom.pr_atom a.neg;
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
      if Options.get_tableaux_cdcl () then
        C_none
      else
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
      if Options.get_debug_sat () then
        Printer.print_dbg ~module_name:"Satml" ~function_name:"simplify" "";
      (*theory_simplify ();*)
      if Vec.size env.learnts > 0 then remove_satisfied env env.learnts;
      if env.remove_satisfied then remove_satisfied env env.clauses;
      (*Iheap.filter env.order f_filter f_weight;*)
      env.simpDB_assigns <- nb_assigns env;
      env.simpDB_props <- env.clauses_literals + env.learnts_literals;
    end


  let record_learnt_clause env ~is_T_learn blevel learnt history =
    let curr_level = decision_level env in
    if not is_T_learn || Options.get_minimal_bj () ||
       blevel = curr_level then begin
      check_levels blevel curr_level;
      match learnt with
      | [] -> assert false
      | [(fuip : Atom.atom)] ->
        fuip.var.vpremise <- history;
        (* Note: there could potentially be semantic values that are no longer
           valid in the union-find at level 0 contained in [fuip] if [fuip] is
           a semantic literal, which could cause crashes -- although it is not
           clear to me that it can really happen since if we learn it at level
           0 it must be explainable by facts at level 0. *)
        enqueue env fuip 0 None
      | fuip :: _ ->
        let name = Atom.fresh_lname () in
        let lclause =
          Atom.make_clause name learnt vraie_form true history
        in
        (* Do not learn clauses involving semantic literals (but still record
           them as a reason for the propagated literal). Learned clauses are
           valid at level 0, but semantic literals can contain terms created by
           the Shostak module that are only useful in a portion of the search
           tree, and in particular would not exist (in Uf) at lower levels.

           Note that we try to avoid semantic literals as much as possible in
           [conflict_analyze_aux], but we can still have semantic decisions
           that would end up in clauses.

           Note that if the [fuip] is itself a semantic literal, it will act as
           a (local) learned clause (see [semantic_expansion]). *)
        let has_split = Vec.exists is_semantic lclause.atoms in
        if not has_split then (
          Vec.push env.learnts lclause;
          attach_clause env lclause;
          clause_bump_activity env lclause
        );
        let propag_lvl = best_propagation_level env lclause in
        enqueue env fuip propag_lvl (Some lclause)
    end;
    if not is_T_learn then begin
      var_decay_activity env;
      clause_decay_activity env
    end

  (* If [a] is a semantic literal that is not a decision, we ideally would
     like to replace it with its reason.

     For instance, if [x = 0] is implied by [a1 /\ .. /\ an] (i.e.  the
     reason for [x = 0] is [x <> 0 \/ not a1 \/ .. \/ not an]) and [x = 0] is
     in conflict with [b] (i.e. we are learning [x <> 0 \/ not b]) we can
     apply resolution to learn [not a1 \/ .. \/ not an \/ not b] instead,
     eliminating the semantic literal [x = 0] in the process. *)
  let rec semantic_expansion env max_lvl blevel learnt seen (a : Atom.atom) =
    assert (a.is_true || a.neg.is_true && a.var.level >= 0);
    assert (a.var.level <= max_lvl);
    if not a.var.seen && a.var.level > 0 then (
      var_bump_activity env a.var;
      a.var.seen <- true;
      seen := a :: !seen;
      match a.var.reason with
      | Some c when is_semantic a ->
        assert a.neg.is_true;
        Vec.iter (fun (b : Atom.atom) ->
            assert (b.neg == a || b.neg.is_true);
            semantic_expansion env max_lvl blevel learnt seen b
          ) c.atoms
      | _ ->
        learnt := SA.add a !learnt;
        blevel := max !blevel a.var.level
    )

  let conflict_analyze_aux env c_clause max_lvl =
    let pathC = ref 0 in
    let learnt = ref SA.empty in
    let cond = ref true in
    let blevel = ref 0 in
    let seen = ref [] in
    let c : Atom.clause ref = ref c_clause in
    let tr_ind = ref (Vec.size env.trail -1) in
    let history = ref [] in
    while !cond do
      if !c.learnt then clause_bump_activity env !c;
      history := !c :: !history;
      Vec.iter (fun (a : Atom.atom) ->
          assert (a.is_true || a.neg.is_true && a.var.level >= 0);
          if not a.var.seen && a.var.level > 0 then begin
            if a.var.level >= max_lvl then begin
              var_bump_activity env a.var;
              a.var.seen <- true;
              seen := a :: !seen;
              incr pathC
            end else begin
              semantic_expansion env a.var.level blevel learnt seen a;
            end
          end
        ) !c.atoms;

      while assert (!tr_ind >= 0);
        let v = (Vec.get env.trail !tr_ind).var in
        not v.seen || ((Options.get_minimal_bj ()) && v.level < max_lvl) do
        decr tr_ind
      done;

      decr pathC;
      let p = Vec.get env.trail !tr_ind in
      decr tr_ind;
      (* Do not use semantic literals as UIPs unless forced to (i.e. there is
         no term UIP and the decision was a semantic literal) *)
      let is_good_uip (p : Atom.atom) =
        match p.var.reason with
        | None -> true
        | Some _ -> not (is_semantic p)
      in
      match !pathC,p.var.reason with
      | 0, _ when is_good_uip p ->
        cond := false;
        learnt := SA.add p.neg !learnt
      | _, None -> assert false
      | _, Some cl -> c := cl
    done;
    List.iter (fun (q : Atom.atom) -> q.var.seen <- false) !seen;
    let learnt = SA.elements !learnt in
    let learnt = List.fast_sort (fun (a : Atom.atom) (b : Atom.atom) ->
        b.var.level - a.var.level) learnt in
    let bj_level =
      if Options.get_minimal_bj () then
        match learnt with
          [] -> 0
        | a :: _ -> max 0 (a.var.level - 1)
      else !blevel
    in
    bj_level, learnt, !history

  let fixable_with_simple_backjump (confl : Atom.clause) max_lvl lv =
    if not (Options.get_minimal_bj ()) then None
    else
      try
        let max_v = ref None in
        let snd_max = ref (-1) in
        List.iter
          (fun (v : Atom.var) ->
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
        | Some (v : Atom.var) ->
          let snd_max = !snd_max in
          assert (snd_max >= 0);
          assert (snd_max < max_lvl);
          assert (not confl.removed); (* do something otherwise ?*)
          let a : Atom.atom = if v.pa.is_true then v.na else v.pa in
          assert (a.neg.is_true);
          assert (max_lvl > 0);
          Some (a, max_lvl - 1, snd_max)
      with Exit -> None

  let conflict_analyze_and_fix env confl =
    env.next_decisions <- [];
    env.next_split <- None;
    env.next_optimized_split <- None;
    env.conflicts <- env.conflicts + 1;
    if decision_level env = 0 then report_conflict env confl;
    match confl with
    | C_none -> assert false
    | C_theory dep ->
      let atoms, max_lvl, c_hist =
        Ex.fold_atoms
          (fun ex (acc, max_lvl, c_hist) ->
             match ex with
             | Ex.Literal a ->
               let c_hist = List.rev_append a.var.vpremise c_hist in
               let c_hist = match a.var.reason with
                 | None -> c_hist | Some r -> r:: c_hist
               in
               if a.var.level = 0 then acc, max_lvl, c_hist
               else a.neg :: acc, max max_lvl a.var.level, c_hist
             | _ -> assert false (* TODO *)
          ) dep ([], 0, [])
      in
      if atoms == [] || max_lvl == 0 then begin
        (* check_inconsistence_of dep; *)
        report_t_unsat env dep
        (* une conjonction de faits unitaires etaient deja unsat *)
      end;
      let name = Atom.fresh_dname() in
      let c = Atom.make_clause name atoms vraie_form false c_hist in
      c.removed <- true;
      let blevel, learnt, history = conflict_analyze_aux env c max_lvl in
      cancel_until env blevel;
      record_learnt_clause env ~is_T_learn:false blevel learnt history

    | C_bool c ->
      let max_lvl = ref 0 in
      let lv = ref [] in
      Vec.iter (fun (a : Atom.atom) ->
          max_lvl := max !max_lvl a.var.level;
          lv := a.var :: !lv
        ) c.atoms;
      if !max_lvl == 0 then report_b_unsat env [c];
      match fixable_with_simple_backjump c !max_lvl !lv with
      | None  ->
        let blevel, learnt, history = conflict_analyze_aux env c !max_lvl in
        cancel_until env blevel;
        record_learnt_clause env ~is_T_learn:false blevel learnt history
      | Some (a, blevel, propag_lvl) ->
        assert (a.neg.is_true);
        cancel_until env blevel;
        assert (not a.neg.is_true);
        assert (propag_lvl >= 0 && propag_lvl <= blevel);
        enqueue env a propag_lvl (Some c)


  let _check_inconsistence_of _ = ()
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
  with Ex.Inconsistent _ -> ()
*)


  type strat =
    | Auto
    | Stop
    | Interactive of Atom.atom

  let find_uip_reason q =
    let res = ref SA.empty in
    let seen = ref SA.empty in
    while not (Queue.is_empty q) do
      let a = Queue.pop q in
      if not (SA.mem a !seen) then begin
        seen := SA.add a !seen;
        match a.var.reason with
        | None when a.var.level = 0 -> ()
        | None ->
          assert (a.is_true || a.neg.is_true);
          res := SA.add (if a.is_true then a else a.neg) !res

        | Some r ->
          Vec.iter
            (fun a -> if not (SA.mem a !seen) then Queue.push a q) r.atoms
      end
    done;
    raise (Last_UIP_reason !res)

  let reason_of_deduction true_atom =
    let q = Queue.create () in
    Queue.push true_atom q;
    try find_uip_reason q
    with Last_UIP_reason r -> r

  let reason_of_conflict (confl_clause : Atom.clause) =
    let q = Queue.create () in
    Vec.iter (fun a -> Queue.push a q) confl_clause.atoms;
    find_uip_reason q

  let rec propagate_and_stabilize env propagator conflictC strat =
    match propagator env with
    | C_none -> ()
    | (C_bool _ | C_theory _ ) as confl -> (* Conflict *)
      let x =
        match strat, confl with
        | Auto, _ -> None
        | _, C_bool confl ->
          (try reason_of_conflict confl
           with Last_UIP_reason r-> Some r)
        | _ -> assert false
      in
      try
        incr conflictC;
        conflict_analyze_and_fix env confl;
        propagate_and_stabilize env propagator conflictC strat;
        if Options.get_tableaux_cdcl () then
          match x with
          | None -> ()
          | Some r -> raise (Last_UIP_reason r)
      with
        Unsat _ as e ->
        if Options.get_tableaux_cdcl () then begin
          if not (Options.get_minimal_bj ()) then
            assert (decision_level env = 0);
          raise (Last_UIP_reason Atom.Set.empty)
        end
        else raise e

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
    if Options.get_no_tcp () || not (Options.get_minimal_bj ()) then None
    else
      match Shostak.Literal.view @@ Atom.literal a with
      | LSem _ -> None
      | LTerm lit ->
        match Th.query lit tenv with
        | Some (d,_) ->
          a.timp <- 1;
          Some (clause_of_dep d a)
        | None  ->
          match Th.query (E.neg lit) tenv with
          | Some (d,_) ->
            a.neg.timp <- 1;
            Some (clause_of_dep d a.Atom.neg)
          | None -> None

  let make_decision env atom =
    match th_entailed env.tenv atom with
    | None ->
      new_decision_level env;
      let current_level = decision_level env in
      env.cpt_current_propagations <- 0;
      assert (atom.var.level < 0);
      if Options.get_debug_sat () then
        Printer.print_dbg "[satml] decide: %a" Atom.pr_atom atom;
      enqueue env atom current_level None
    | Some (c, _) ->
      (* right decision level will be set inside record_learnt_clause *)
      record_learnt_clause env ~is_T_learn:true (decision_level env) c []

  let rec pick_branch_aux env (atom : Atom.atom) =
    let v = atom.var in
    if v.level >= 0 then begin
      assert (v.pa.is_true || v.na.is_true);
      pick_branch_lit env
    end else if Options.get_cdcl_tableaux_inst () then
      (* Do not decide on irrelevant variables (e.g. if we know [P] is true and
         the only relevant formula involving [Q] is [P \/ Q], deciding on [Q] is
         unlikely to be helpful -- especially since irrelevant decision won't be
         propagated to the theory).

         Note that we can only do this if [get_cdcl_tableaux_inst ()] is [true],
         because otherwise instantiation requires a complete boolean model. *)
      if is_relevant env v then
        make_decision env atom
      else (
        VH.add env.irrelevants v ();
        pick_branch_lit env
      )
    else
      make_decision env atom

  and pick_branch_lit env =
    match env.next_optimized_split with
    | Some (fn, value, atom) ->
      env.next_optimized_split <- None;
      let v = atom.var in
      if v.level >= 0 then (
        assert (v.pa.is_true || v.na.is_true);
        if atom.is_true then
          env.tenv <- Th.add_objective env.tenv fn value;
        pick_branch_lit env
      ) else (
        make_decision env atom;
        if atom.is_true then
          env.tenv <- Th.add_objective env.tenv fn value
      )
    | None ->
      match env.next_decisions with
      | atom :: tl ->
        env.next_decisions <- tl;
        pick_branch_aux env atom
      | [] ->
        match env.next_split with
        | Some atom ->
          env.next_split <- None;
          pick_branch_aux env atom
        | None ->
          match Vheap.pop_min env.order with
          | v -> pick_branch_aux env v.na
          | exception Not_found ->
            if Options.get_cdcl_tableaux_inst () then
              assert (Matoms.is_empty env.lazy_cnf);
            raise_notrace Sat

  let pick_branch_lit env =
    if env.next_dec_guard < Vec.size env.increm_guards then
      begin
        let a = Vec.get env.increm_guards env.next_dec_guard in
        (assert (not (a.neg.is_guard || a.neg.is_true)));
        env.next_dec_guard <- env.next_dec_guard + 1;
        make_decision env a;
        let fns = Vec.get env.objectives (env.next_dec_guard-1) in
        let tenv =
          List.fold_right
            (fun fn tenv ->
               Th.add_objective tenv fn Objective.Value.Unknown
            ) fns env.tenv
        in
        env.tenv <- tenv;
      end
    else
      pick_branch_lit env

  let is_sat env =
    env.next_dec_guard = Vec.size env.increm_guards &&
    Option.is_none env.next_optimized_split &&
    Compat.List.is_empty env.next_decisions &&
    Option.is_none env.next_split && (
      nb_assigns env = nb_vars env ||
      (Options.get_cdcl_tableaux_inst () &&
       Matoms.is_empty env.lazy_cnf))

  let search env strat n_of_conflicts n_of_learnts =
    let conflictC = ref 0 in
    env.starts <- env.starts + 1;
    while true do
      propagate_and_stabilize env all_propagations conflictC !strat;

      if is_sat env then
        raise Sat;
      if Options.get_enable_restarts ()
      && n_of_conflicts >= 0 && !conflictC >= n_of_conflicts then begin
        (*         env.progress_estimate <- progress_estimate env; *)
        cancel_until env 0;
        raise Restart
      end;
      if decision_level env = 0 then simplify env;

      if n_of_learnts >= 0 &&
         Vec.size env.learnts - nb_assigns env >= n_of_learnts then
        reduce_db();

      match !strat with
      | Auto -> pick_branch_lit env
      | Stop -> raise Stopped
      | Interactive f ->
        strat := Stop;
        make_decision env f
    done

  (* unused --
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
  *)

  let solve env =
    if env.is_unsat then raise (Unsat env.unsat_core);
    let n_of_conflicts = ref (Atom.to_float env.restart_first) in
    let n_of_learnts =
      ref ((Atom.to_float (nb_clauses env)) *. env.learntsize_factor) in
    try
      while true do
        (try search env (ref Auto)
               (Atom.to_int !n_of_conflicts) (Atom.to_int !n_of_learnts);
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
    | (Unsat _) as e ->
      (* check_unsat_core cl; *)
      raise e

  let rec compute_concrete_model ~declared_ids env =
    let acts = theory_slice env in
    match Th.compute_concrete_model ~acts env.tenv with
    | () -> (
        if is_sat env then
          Th.extract_concrete_model ~declared_ids env.tenv
        else
          try
            solve env; assert false
          with Sat ->
            compute_concrete_model ~declared_ids env
      )
    | exception Ex.Inconsistent (ex, _) ->
      conflict_analyze_and_fix env (C_theory ex);
      compute_concrete_model ~declared_ids env

  exception Trivial

  let partition atoms init =
    let rec partition_aux trues unassigned falses init = function
      | [] -> trues @ unassigned @ falses, init
      | (a : Atom.atom)::r ->
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
      if Options.get_unsat_core () then
        [Atom.make_clause init_name atoms f false []]
      else
        [] (* no deps if unsat cores generation is not enabled *)
    in
    try
      let atoms, init =
        if decision_level env = 0 then
          let atoms, init = List.fold_left
              (fun (atoms, init) (a : Atom.atom) ->
                 if a.is_true then raise Trivial;
                 if a.neg.is_true then begin
                   if Options.get_profiling() then Profiling.red true;
                   atoms, (List.rev_append (a.var.vpremise) init)
                 end
                 else a::atoms, init
              ) ([], init0) atoms in
          List.fast_sort (fun a b ->
              Atom.compare_var a.Atom.var b.Atom.var
            ) atoms, init
        else partition atoms init0
      in
      match atoms with
      | [] ->
        report_b_unsat env init0;

      | a::b::_ ->
        let name = Atom.fresh_name () in
        let clause = Atom.make_clause name atoms vraie_form false init in
        attach_clause env clause;
        Vec.push env.clauses clause;
        if Options.(get_debug_sat () && get_verbose ()) then
          Printer.print_dbg ~module_name:"Satml" ~function_name:"add_clause"
            "add_clause: %a" Atom.pr_clause clause;

        if a.neg.is_true then begin (* clause is false *)
          let lvl =
            List.fold_left (fun m (a : Atom.atom) -> max m a.var.level) 0 atoms
          in
          cancel_until env lvl;
          conflict_analyze_and_fix env (C_bool clause)
        end
        else
        if not a.is_true && b.neg.is_true then
          begin (* clause is unit *)
            let mlvl = best_propagation_level env clause in
            enqueue env a mlvl (Some clause);
          end
          [@ocaml.ppwarning "TODO: add a heavy assert that checks \
                             that clauses are not redundant, watchs \
                             are well set, unit and bottom are \
                             detected ..."]
      | [a]   ->
        if Options.(get_debug_sat () && get_verbose ()) then
          Printer.print_dbg ~module_name:"Satml" ~function_name:"add_clause"
            "add_atom: %a" Atom.pr_atom a;
        let lvl = a.var.level in
        assert (lvl <> 0);
        begin
          if not (Options.get_minimal_bj ()) then cancel_until env 0
          else if a.is_true || a.neg.is_true then cancel_until env (lvl - 1)
        end;
        a.var.vpremise <- init;
        enqueue env a 0 None;
        propagate_and_stabilize env propagate (ref 0) Auto
    (* TODO *)

    with Trivial ->
      if Options.get_profiling() then Profiling.elim true


  let update_lazy_cnf env ~do_bcp sff ~dec_lvl =
    if Options.get_cdcl_tableaux () && dec_lvl <= decision_level env then begin
      let s =
        try Util.MI.find dec_lvl env.lvl_ff
        with Not_found -> SFF.empty
      in
      let lz, s =
        SFF.fold (fun ff (l, s) ->
            assert (not (MFF.mem ff env.ff_lvl));
            assert (not (SFF.mem ff s));
            env.ff_lvl <- MFF.add ff dec_lvl env.ff_lvl;
            add_form_to_lazy_cnf env l ff, SFF.add ff s
          ) sff (env.lazy_cnf, s)
      in
      env.lazy_cnf <- lz;
      env.lvl_ff <- Util.MI.add dec_lvl s env.lvl_ff;
      if do_bcp then
        propagate_and_stabilize (*theory_propagate_opt*)
          env all_propagations (ref 0) Auto;
    end

  let new_vars env ~nbv new_v unit_cnf nunit_cnf  =
    match new_v with
    | [] -> unit_cnf, nunit_cnf
    | _ ->
      let tenv0 = env.unit_tenv in
      Vec.grow_to_by_double env.vars nbv;
      Vheap.grow_to_by_double env.order nbv;
      let accu =
        List.fold_left
          (fun ((unit_cnf, nunit_cnf) as accu) (v : Atom.var) ->
             Vec.push env.vars v;
             assert (not (is_semantic v.pa));
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
      (* This assert is no longer true because some of the vars in the
         [hcons_env] are now semantic literals.
         assert (nbv = Vec.size env.vars); *)
      accu

  let set_new_proxies env proxies =
    env.proxies <- proxies

  let try_to_backjump_further =
    let rec better_bj env sf =
      (* If we *don't* backjump further, we need to restore any part of the
         environment that depends on the theory. *)
      let old_dlvl = decision_level env in
      let old_lazy = env.lazy_cnf in
      let old_relevants = env.relevants in
      let old_tenv = env.tenv in
      let old_decisions = env.next_decisions in
      let old_split = env.next_split in
      let old_optimized_split = env.next_optimized_split in
      let fictive_lazy =
        SFF.fold (fun ff acc -> add_form_to_lazy_cnf env acc ff)
          sf old_lazy
      in
      env.lazy_cnf <- fictive_lazy;
      propagate_and_stabilize env all_propagations (ref 0) Auto;
      let new_dlvl = decision_level env in
      if old_dlvl > new_dlvl then better_bj env sf
      else
        begin
          assert (old_dlvl == new_dlvl);
          env.lazy_cnf <- old_lazy;
          env.relevants <- old_relevants;
          env.tenv     <- old_tenv;
          env.next_decisions <- old_decisions;
          env.next_split <- old_split;
          env.next_optimized_split <- old_optimized_split
        end
    in
    fun env sff ->
      if Options.get_cdcl_tableaux () then
        better_bj env sff


  let assume env unit_cnf nunit_cnf f ~cnumber sff ~dec_lvl =
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

        if Options.get_verbose () then
          Printer.print_dbg
            "%d clauses@ %d learnts"
            (Vec.size env.clauses)
            (Vec.size env.learnts);
    end;
    (* do it after add clause and before T-propagate, disable bcp*)
    update_lazy_cnf env ~do_bcp:false sff ~dec_lvl;
    (* do bcp globally *)
    propagate_and_stabilize env all_propagations (ref 0) Auto;
    if dec_lvl > decision_level env then
      (*dec_lvl <> 0 and a bj have been made*)
      try_to_backjump_further env sff

  let exists_in_lazy_cnf env f' =
    not (Options.get_cdcl_tableaux ()) ||
    MFF.mem f' env.ff_lvl

  let boolean_model env = Vec.to_list env.trail

  let instantiation_context env hcons =
    if Options.get_cdcl_tableaux_th () then
      (* use atoms from theory environment if tableaux method
         is used for theories *)
      E.Set.fold
        (fun a accu ->
           SA.add (FF.get_atom hcons a) accu
        )(Th.get_assumed env.tenv) SA.empty
    else if Options.get_cdcl_tableaux_inst () then
      (* use relevants atoms from environment if tableaux method
         is used for instantiation *)
      SFF.fold (fun f acc ->
          match FF.view f with
          | FF.UNIT a -> SA.add a acc
          | _ -> acc
        )env.relevants SA.empty
    else
      (* can't be call if tableaux method is not used *)
      assert false

  let current_tbox env = env.tenv
  let set_current_tbox env tb = env.tenv <- tb

  let assume_th_elt env th_elt dep =
    assert (decision_level env == 0);
    env.tenv <- Th.assume_th_elt (current_tbox env) th_elt dep

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

  (* HYBRID SAT functions *)
  let assume_simple env cnf =
    match cnf with
    | [] -> ()
    | _ ->
      let nbc = env.nb_init_clauses + List.length cnf in
      Vec.grow_to_by_double env.clauses nbc;
      Vec.grow_to_by_double env.learnts nbc;
      env.nb_init_clauses <- nbc;

      List.iter (add_clause env vraie_form ~cnumber:0) cnf;

      if Options.get_verbose () then
        Printer.print_dbg
          "%d clauses@ %d learnts"
          (Vec.size env.clauses)
          (Vec.size env.learnts);

      (* do it after add clause and before T-propagate, disable bcp*)
      (* do bcp globally *)
      propagate_and_stabilize env all_propagations (ref 0) Stop


  let decide env f =
    if env.is_unsat then raise (Unsat env.unsat_core);
    let n_of_conflicts = ref (Atom.to_float env.restart_first) in
    let n_of_learnts =
      ref ((Atom.to_float (nb_clauses env)) *. env.learntsize_factor) in
    try
      search env (ref (Interactive f))
        (Atom.to_int !n_of_conflicts) (Atom.to_int !n_of_learnts);
    with
    | Restart -> assert false
    | Sat -> ()
    | Stopped -> ()
    | Unsat _ -> assert false

  let push env guard =
    assert (not (is_assigned guard));
    guard.is_guard <- true;
    guard.neg.is_guard <- false;
    cancel_until env env.next_dec_guard;
    Vec.push env.increm_guards guard;
    Vec.push env.objectives []

  let pop env =
    assert (not (Vec.is_empty env.increm_guards));
    let g = Vec.pop env.increm_guards in
    let _ = Vec.pop env.objectives in
    g.is_guard <- false;
    g.neg.is_guard <- false;
    assert (not g.var.na.is_true); (* atom not false *)
    if g.var.pa.is_true then (* if already decided  *)
      begin
        (assert (g.var.level > 0));
        cancel_until env (g.var.level - 1); (* undo its decision *)
        (* all previous guards are decided *)
        env.next_dec_guard <- Vec.size env.increm_guards
      end
    else
      (* We are not decided, so the `next_dec_guard` should point to an
         earlier guard or we have a bug because guards must be decided in
         the `increm_guards` order. *)
      assert (env.next_dec_guard <= Vec.size env.increm_guards);
    enqueue env g.neg 0 None

  let optimize env fn =
    if decision_level env > 0 then Fmt.invalid_arg "Satml.optimize";
    if Vec.size env.increm_guards = 0 then
      env.tenv <- Th.add_objective env.tenv fn Objective.Value.Unknown
    else
      Vec.replace (fun fns -> fn :: fns) env.objectives
        (Vec.size env.objectives - 1)
end
