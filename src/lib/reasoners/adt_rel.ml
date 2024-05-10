(**************************************************************************)
(*                                                                        *)
(*     Alt-Ergo: The SMT Solver For Software Verification                 *)
(*     Copyright (C) 2013-2023 --- OCamlPro SAS                           *)
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
(*     Until 2013, some parts of this code were released under            *)
(*     the Apache Software License version 2.0.                           *)
(*                                                                        *)
(*     ---------------------------------------------------------------    *)
(*                                                                        *)
(*     More details can be found in the directory licenses/               *)
(*                                                                        *)
(**************************************************************************)

module X = Shostak.Combine
module Ex = Explanation
module E = Expr
module SE = E.Set
module Sy = Symbols
module MX = Shostak.MXH
module SX = Shostak.SXH
module LR = Uf.LX
module Th = Shostak.Adt
module SLR = Set.Make(LR)

let timer = Timers.M_Adt

module Domain = struct
  (* Set of possible constructors. The explanation justifies that any value
     assigned to the semantic value has to use a constructor lying in the
     domain. *)
  type t = {
    constrs : Uid.Set.t;
    ex : Ex.t;
  }

  exception Inconsistent of Ex.t

  let[@inline always] as_singleton { constrs; ex } =
    if Uid.Set.cardinal constrs = 1 then
      Some (Uid.Set.choose constrs, ex)
    else
      None

  let domain ~constrs ex =
    if Uid.Set.is_empty constrs then
      raise @@ Inconsistent ex
    else
      { constrs; ex }

  let[@inline always] singleton ~ex c = { constrs = Uid.Set.singleton c; ex }

  let[@inline always] subset d1 d2 = Uid.Set.subset d1.constrs d2.constrs

  let unknown ty =
    match ty with
    | Ty.Tadt (name, params) ->
      (* Return the list of all the constructors of the type of [r]. *)
      let Adt body = Ty.type_body name params in
      let constrs =
        List.fold_left
          (fun acc Ty.{ constr; _ } ->
             Uid.Set.add constr acc
          ) Uid.Set.empty body
      in
      assert (not @@ Uid.Set.is_empty constrs);
      { constrs; ex = Ex.empty }
    | _ ->
      (* Only ADT values can have a domain. This case shouldn't happen since
         we check the type of semantic values in both [add] and [assume]. *)
      assert false

  let equal d1 d2 = Uid.Set.equal d1.constrs d2.constrs

  let pp ppf d =
    Fmt.(braces @@
         iter ~sep:comma Uid.Set.iter Uid.pp) ppf d.constrs;
    if Options.(get_verbose () || get_unsat_core ()) then
      Fmt.pf ppf " %a" (Fmt.box Ex.print) d.ex

  let intersect ~ex d1 d2 =
    let constrs = Uid.Set.inter d1.constrs d2.constrs in
    let ex = ex |> Ex.union d1.ex |> Ex.union d2.ex in
    domain ~constrs ex

  let remove ~ex c d =
    let constrs = Uid.Set.remove c d.constrs in
    let ex = Ex.union ex d.ex in
    domain ~constrs ex
end

module Domains = struct
  (** The type of simple domain maps. A domain map maps each representative
      (semantic value, of type [X.r]) to its associated domain. *)
  type t = {
    domains : Domain.t MX.t;
    (** Map from tracked representatives to their domain.

        We don't store domains for constructors and selectors. *)

    changed : SX.t;
    (** Representatives whose domain has changed since the last flush
        in [propagation]. *)
  }

  let pp ppf t =
    Fmt.(iter_bindings ~sep:semi MX.iter
           (box @@ pair ~sep:(any " ->@ ") X.print Domain.pp)
         |> braces
        )
      ppf t.domains

  let empty = { domains = MX.empty; changed = SX.empty }

  let internal_update r nd t =
    let domains = MX.add r nd t.domains in
    let changed = SX.add r t.changed in
    { domains; changed }

  let get r t =
    match Th.embed r with
    | Constr { c_name; _ } ->
      (* For sake of efficiency, we don't look in the map if the
         semantic value is a constructor. *)
      Domain.singleton ~ex:Explanation.empty c_name
    | _ ->
      try MX.find r t.domains
      with Not_found ->
        Domain.unknown (X.type_info r)

  let add r t =
    if MX.mem r t.domains then t
    else
      match Th.embed r with
      | Constr _ | Select _ -> t
      | Alien _ ->
        (* We have to add a default domain if the key `r` isn't in map in order
           to be sure that the case-split mechanism will attempt to choose a
           value for it. *)
        let nd = Domain.unknown (X.type_info r) in
        internal_update r nd t

  (** [tighten r d t] replaces the domain of [r] in [t] by a domain [d] contains
      in the current domain of [r]. The representative [r] is marked [changed]
      after this call if the domain [d] is strictly smaller. *)
  let tighten r d t =
    let od = get r t in
    (* For sake of completeness, the domain [d] has to be a subset of the old
       domain of [r]. *)
    Options.heavy_assert (fun () -> Domain.subset d od);
    if Domain.equal od d then
      t
    else
      internal_update r d t

  let remove r t =
    let domains = MX.remove r t.domains in
    let changed = SX.remove r t.changed in
    { domains ; changed }

  (** [subst ~ex p v d] replaces all the instances of [p] with [v] in all
      domains, merging the corresponding domains as appropriate.

      The explanation [ex] justifies the equality [p = v].

      @raise Domain.Inconsistent if this causes any domain in [d] to become
             empty. *)
  let subst ~ex r nr t =
    match MX.find r t.domains with
    | d ->
      let nd = Domain.intersect ~ex d (get nr t) in
      let t = remove r t in
      tighten nr nd t

    | exception Not_found -> t

  (* [propagate f a t] iterates on all the changed domains of [t] since the
     last call of [propagate]. The list of changed domains is flushed after
     this call. *)
  let propagate f acc t =
    let acc =
      SX.fold
        (fun r acc ->
           let d = get r t in
           f acc r d
        ) t.changed acc
    in
    acc, { t with changed = SX.empty }
end

let calc_destructor d e uf =
  let r, ex = Uf.find uf e in
  match Th.embed r with
  | Constr { c_args; _ } ->
    begin match Lists.assoc Uid.equal d c_args with
      | v -> Some (v, ex)
      | exception Not_found -> None
    end

  | _ ->
    None

let delayed_destructor uf op = function
  | [e] ->
    begin match op with
      | Sy.Destruct d ->
        calc_destructor d e uf
      | _ -> assert false
    end
  | _ -> assert false

let is_ready r =
  match Th.embed r with
  | Constr _ -> true
  | _ -> false

let dispatch = function
  | Symbols.Destruct _ -> Some delayed_destructor
  | _ -> None

type t = {
  classes : E.Set.t list;
  (* State of the union-find represented by all its equivalence classes.
     This state is kept for debugging purposes only. It is updated after
     assuming literals of the theory and returned by queries in case of
     inconsistency. *)

  domains : Domains.t;

  delayed : Rel_utils.Delayed.t;
  (* Set of delayed destructor applications. The computation of a destructor
     application [d r] is forced if we see the tester `(_ is d) r` of the
     associated constructor [c] of [d]. *)

  size_splits : Numbers.Q.t;
  (* Product of the size of all the facts learnt by CS assumed in
     the theory.

     Currently this field is unused. *)

  new_terms : SE.t;
  (* Set of all the constructor applications built by the theory.
     See the function [deduce_is_constr]. *)
}

let empty classes = {
  classes;
  domains = Domains.empty;
  delayed = Rel_utils.Delayed.create ~is_ready dispatch;
  size_splits = Numbers.Q.one;
  new_terms = SE.empty;
}

(* ################################################################ *)
(*BISECT-IGNORE-BEGIN*)
module Debug = struct
  open Printer

  let assume a =
    if Options.get_debug_adt () then
      print_dbg
        ~module_name:"Adt_rel"
        ~function_name:"assume"
        "assume %a" LR.print (LR.make a)

  let pp_env loc env =
    if Options.get_debug_adt () then begin
      print_dbg ~flushed:false ~module_name:"Adt_rel"
        "@[<v 2>--ADT env %s ---------------------------------@ " loc;
      print_dbg ~flushed:false ~header:false "domains:@ %a"
        Domains.pp env.domains;
      print_dbg ~header:false "---------------------"
    end

  (* unused --
     let case_split r r' =
     if get_debug_adt () then
       Printer.print_dbg
          "[ADT.case-split] %a = %a" X.print r X.print r'
  *)

  let no_case_split () =
    if Options.get_debug_adt () then
      print_dbg
        ~module_name:"Adt_rel"
        ~function_name:"case-split"
        "nothing"

  let add r =
    if Options.get_debug_adt () then
      print_dbg
        ~module_name:"Adt_rel"
        ~function_name:"add"
        "%a" X.print r

end
(*BISECT-IGNORE-END*)
(* ################################################################ *)


let[@inline always] new_terms env = env.new_terms

let instantiate ~do_syntactic_matching:_ _ env _ _ = env, []

let assume_th_elt t th_elt _ =
  match th_elt.Expr.extends with
  | Util.Adt ->
    failwith "This Theory does not support theories extension"
  | _ -> t

let tighten_domain r nd env =
  { env with domains = Domains.tighten r nd env.domains }

(* Update the domains of the semantic values [r1] and [r2] according to
   the substitution `r1 |-> r2`.

   @raise Domain.Inconsistent if this substitution is inconsistent with
          the current environment [env]. *)
let assume_subst ~ex r1 r2 env =
  let domains = Domains.subst ~ex r1 r2 env.domains in
  { env with domains }

(* Update the domains of the semantic values [r1] and [r2] according to the
   disequality [r1 <> r2].

   This function alone isn't sufficient to produce a complete decision
   procedure for the ADT theory. For instance, let's assume we have three
   semantic values [r1], [r2] and [r3] whose the domain is `{C1, C2}`. It's
   clear that `(distinct r1 r2 r3)` is unsatisfiable but we haven't enough
   information to discover this contradiction.

   We plan to support model generation for ADT. As a by-product, we will got
   a complete decision procedure for the ADT through the case-split mechanism
   as we did in the Enum theory.

   @raise Domain.Inconsistent if the disequality is inconsistent with
          the current environment [env]. *)
let assume_distinct =
  let aux ~ex r1 r2 env =
    match Th.embed r1 with
    | Constr { c_args; _ } when List.length c_args = 0 ->
      begin
        let d1 = Domains.get r1 env.domains in
        let d2 = Domains.get r2 env.domains in
        match Domain.as_singleton d1 with
        | Some (c, ex') ->
          let ex = Ex.union ex ex' in
          let nd = Domain.remove ~ex c d2 in
          tighten_domain r2 nd env
        | None -> env
      end
    | _ ->
      (* If `d1` is a singleton domain but its constructor has a payload,
         we cannot tighten the domain of `r2` because they could have
         distinct payloads. *)
      env
  in fun ~ex r1 r2 env ->
    aux ~ex r1 r2 env |> aux ~ex r2 r1

(* Assumes the tester `((_ is c) r)` where [r] can be a constructor
   application or a uninterpreted semantic value.

   @raise Domain.Inconsistent if we already know that the value of [r]
          cannot be an application of the constructor [c]. *)
let assume_is_constr ~ex r c env =
  let d1 = Domains.get r env.domains in
  let d2 = Domain.singleton ~ex:Explanation.empty c in
  let nd = Domain.intersect ~ex d1 d2 in
  tighten_domain r nd env

(* Assume `(not ((_ is c) r))` where [r] can be a constructor application
   or a uninterpreted semantic value.

   We remove the destructor equations associated with [r] and [c].

   @raise Domain.Inconsistent if we already know that the value of [r] has to
          be an application of the constructor [c]. *)
let assume_not_is_constr ~ex r c env =
  let d = Domains.get r env.domains in
  let nd = Domain.remove ~ex c d in
  tighten_domain r nd env

let add r uf env =
  match X.type_info r with
  | Ty.Tadt _ ->
    Debug.add r;
    let rr, _ = Uf.find_r uf r in
    { env with domains = Domains.add rr env.domains }
  | _ ->
    env

let is_adt r =
  match X.type_info r with
  | Ty.Tadt _ -> true
  | _ -> false

let add_rec r uf env =
  List.fold_left (fun env lf -> add lf uf env) env (X.leaves r)

let add env uf r t =
  if Options.get_disable_adts () then
    env, []
  else
    let env = add r uf env in
    let delayed, eqs = Rel_utils.Delayed.add env.delayed uf r t in
    { env with delayed }, eqs

let assume_literals la uf env =
  List.fold_left
    (fun env lit ->
       let open Xliteral in
       match lit with
       | Eq (r1, r2) as l, _, ex, Th_util.Subst when is_adt r1 ->
         Debug.assume l;
         (* Needed for models generation because fresh terms are not added with
            the function add. *)
         let env = add_rec r1 uf env in
         let env = add_rec r2 uf env in
         assume_subst ~ex r1 r2 env

       | Distinct (false, [r1; r2]) as l, _, ex, _ when is_adt r2 ->
         Debug.assume l;
         let rr1, ex1 = Uf.find_r uf r1 in
         let rr2, ex2 = Uf.find_r uf r2 in
         (* The explanation [ex] explains why [r1] and [r2] are distinct,
            which isn't sufficient to justify why [rr1] and [rr2] are
            distinct. *)
         let ex = Ex.union ex1 @@ Ex.union ex2 ex in
         (* Needed for models generation because fresh terms are not added with
            the function add. *)
         let env = add_rec rr1 uf env in
         let env = add_rec rr2 uf env in
         assume_distinct ~ex rr1 rr2 env

       | Builtin (true, Sy.IsConstr c, [r]) as l, _, ex, _ ->
         Debug.assume l;
         let r, ex1 = Uf.find_r uf r in
         let ex = Ex.union ex1 ex in
         assume_is_constr ~ex r c env

       | Builtin (false, Sy.IsConstr c, [r]) as l, _, ex, _ ->
         Debug.assume l;
         let r, ex1 = Uf.find_r uf r in
         let ex = Ex.union ex1 ex in
         assume_not_is_constr ~ex r c env

       | _ ->
         (* We ignore [Eq] literals that aren't substitutions as the propagation
            of such equalities will produce substitutions later.
            More precisely, the equation [Eq (r1, r2)] will produce two
            substitutions:
              [Eq (r1, rr)] and [Eq (r2, rr)]
            where [rr] is the new class representative. *)
         env
    ) env la

(* For a uninterpreted semantic value [r] and [c] a constructor of the form:
     (cons (d1 ty1) ... (dn tyn))
   this function creates the equation:
     [t = cons x1 ... xn]
   where x1, ..., xn are fresh names of type respectively ty1, ..., tyn
   and [t] is the term associated with the uninterpreted semantic value [r].

   Assume that [r] is a contructor application of an alien semantic value
   of type [Ty.Adt]. *)
let build_constr_eq r c =
  match Th.embed r with
  | Alien r ->
    begin match X.type_info r with
      | Ty.Tadt (name, params) as ty ->
        let Ty.Adt body = Ty.type_body name params in
        let ds =
          try Ty.assoc_destrs c body with Not_found -> assert false
        in
        let xs = List.map (fun (_, ty) -> E.fresh_name ty) ds in
        let cons = E.mk_constr c xs ty in
        let r', ctx = X.make cons in
        (* In the current implementation of `X.make`, we produce
           a nonempty context only for interpreted semantic values
           of the `Arith` and `Records` theories. The semantic
           values `cons` never involves such values. *)
        assert (Lists.is_empty ctx);
        let eq = Shostak.L.(view @@ mk_eq r r') in
        Some (eq, E.mk_constr c xs ty)

      | _ -> assert false
    end

  | Constr _ ->
    (* The semantic value [r] is already a constructor application, so
       we don't need to produce a new equation in this case. *)
    None

  | Select _ ->
    assert false

let propagate_domains env =
  Domains.propagate
    (fun (eqs, new_terms) rr d ->
       match Domain.as_singleton d with
       | Some (c, ex) ->
         begin match build_constr_eq rr c with
           | Some (eq, cons) ->
             let new_terms = SE.add cons new_terms in
             (Literal.LSem eq, ex, Th_util.Other) :: eqs, new_terms
           | None ->
             eqs, new_terms
         end
       | None ->
         eqs, new_terms
    ) ([], env.new_terms) env.domains

(* Remove duplicate literals in the list [la]. *)
let remove_redundancies la =
  let cache = ref SLR.empty in
  List.filter
    (fun (a, _, _, _) ->
       let a = LR.make a in
       if SLR.mem a !cache then false
       else begin
         cache := SLR.add a !cache;
         true
       end
    ) la

(* Update the counter of case-split size in [env]. *)
let count_splits env la =
  List.fold_left
    (fun nb (_, _, _, i) ->
       match i with
       | Th_util.CS (Th_util.Th_adt, n) -> Numbers.Q.mult nb n
       | _ -> nb
    ) env.size_splits la

let assume env uf la =
  Debug.pp_env "before assume" env;
  (* should be done globally in CCX *)
  let la = remove_redundancies la in
  let delayed, result = Rel_utils.Delayed.assume env.delayed uf la in
  let env =
    try
      assume_literals la uf env
    with Domain.Inconsistent ex ->
      raise_notrace (Ex.Inconsistent (ex, env.classes))
  in
  let (assume, new_terms), domains = propagate_domains env in
  let assume = List.rev_append assume result.assume in
  let env = {
    delayed; domains;
    classes = Uf.cl_extract uf;
    size_splits = count_splits env la;
    new_terms;
  }
  in
  Debug.pp_env "after assume" env;
  env, Sig_rel.{ assume; remove = [] }

(* ################################################################ *)

let two = Numbers.Q.from_int 2

(* Find the constructor associated with the destructor [d] in the ADT [ty].

   requires: [d] is a destructor of [ty]. *)
(* TODO: we should compute this reverse map in `Ty` and store it there. *)
let constr_of_destr ty d =
  match ty with
  | Ty.Tadt (name, params) ->
    begin
      let Ty.Adt cases = Ty.type_body name params in
      try
        let r =
          List.find
            (fun Ty.{ destrs; _ } ->
               List.exists (fun (d', _) -> Uid.equal d d') destrs
            ) cases
        in
        r.constr
      with Not_found -> assert false
    end

  | _ -> assert false

exception Found of X.r * Uid.t

(* Pick a delayed destructor application in [env.delayed]. Returns [None]
   if there is no delayed destructor. *)
let pick_delayed_destructor env =
  try
    Rel_utils.Delayed.iter_delayed
      (fun r sy _e ->
         match sy with
         | Sy.Destruct d ->
           raise_notrace @@ Found (r, d)
         | _ ->
           ()
      ) env.delayed;
    None
  with Found (r, d) -> Some (r, d)

(* Do a case-split by choosing a semantic value [r] and constructor [c]
   for which there are delayed destructor applications and propagate the
   literal [(not (_ is c) r)]. *)
let case_split env _uf ~for_model =
  if Options.get_disable_adts () || not (Options.get_enable_adts_cs())
  then
    []
  else begin
    assert (not for_model);
    if Options.get_debug_adt () then Debug.pp_env "before cs" env;
    match pick_delayed_destructor env with
    | Some (r, d) ->
      if Options.get_debug_adt () then
        Printer.print_dbg ~flushed:false
          ~module_name:"Adt_rel" ~function_name:"case_split"
          "found r = %a and d = %a@ " X.print r Uid.pp d;
      (* CS on negative version would be better in general. *)
      let c = constr_of_destr (X.type_info r) d in
      let cs =  LR.mkv_builtin false (Sy.IsConstr c) [r] in
      [ cs, true, Th_util.CS (Th_util.Th_adt, two) ]
    | None ->
      Debug.no_case_split ();
      []
  end

let optimizing_objective _env _uf _o = None

let query env uf (ra, _, ex, _) =
  if Options.get_disable_adts () then None
  else
    try
      match ra with
      | Xliteral.Builtin(true, Sy.IsConstr c, [r]) ->
        let rr, _ = Uf.find_r uf r in
        ignore (assume_is_constr ~ex rr c env);
        None

      | Xliteral.Builtin(false, Sy.IsConstr c, [r]) ->
        let rr, _ = Uf.find_r uf r in
        ignore (assume_not_is_constr ~ex rr c env);
        None

      | _ ->
        None
    with
    | Domain.Inconsistent ex -> Some (ex, env.classes)

(* ################################################################ *)
