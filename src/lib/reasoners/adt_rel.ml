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
module SE = E.Set
module Sy = Symbols
module MX = Shostak.MXH
module SX = Shostak.SXH
module LR = Uf.LX
module Th = Shostak.Adt
module SLR = Set.Make(LR)

module DE = Dolmen.Std.Expr
module DT = Dolmen.Std.Expr.Ty
module B = Dolmen.Std.Builtin

let src = Logs.Src.create ~doc:"Adt_rel" __MODULE__
module Log = (val Logs.src_log src : Logs.LOG)

module TSet =
  Set.Make
    (struct
      type t = DE.term_cst

      (* We use a dedicated total order on the constructors to ensure
         the termination of model generation. *)
      let compare id1 id2 =
        Nest.perfect_hash id1 - Nest.perfect_hash id2
    end)

let timer = Timers.M_Adt

module Domain = struct
  (* Set of possible constructors. The explanation justifies that any value
     assigned to the semantic value has to use a constructor lying in the
     domain. *)
  type t = {
    constrs : TSet.t;
    ex : Ex.t;
  }

  exception Inconsistent of Ex.t

  let[@inline always] cardinal { constrs; _ } = TSet.cardinal constrs

  let[@inline always] choose { constrs; _ } =
    (* We choose the minimal element to ensure the termination of
       model generation. *)
    TSet.min_elt constrs

  let[@inline always] as_singleton { constrs; ex } =
    if TSet.cardinal constrs = 1 then
      Some (TSet.choose constrs, ex)
    else
      None

  let domain ~constrs ex =
    if TSet.is_empty constrs then
      raise @@ Inconsistent ex
    else
      { constrs; ex }

  let[@inline always] singleton ~ex c =
    { constrs = TSet.singleton c; ex }

  let[@inline always] subset d1 d2 = TSet.subset d1.constrs d2.constrs

  let unknown ty =
    match ty with
    | Ty.Tadt (name, params) ->
      (* Return the list of all the constructors of the type of [r]. *)
      let cases = Ty.type_body name params in
      let constrs =
        List.fold_left
          (fun acc Ty.{ constr; _ } ->
             TSet.add constr acc
          ) TSet.empty cases
      in
      assert (not @@ TSet.is_empty constrs);
      { constrs; ex = Ex.empty }
    | _ ->
      (* Only ADT values can have a domain. This case shouldn't happen since
         we check the type of semantic values in both [add] and [assume]. *)
      assert false

  let equal d1 d2 = TSet.equal d1.constrs d2.constrs

  let pp ppf d =
    Fmt.(braces @@
         iter ~sep:comma TSet.iter DE.Term.Const.print) ppf d.constrs;
    if Options.(get_verbose () || get_unsat_core ()) then
      Fmt.pf ppf " %a" (Fmt.box Ex.print) d.ex

  let intersect ~ex d1 d2 =
    let constrs = TSet.inter d1.constrs d2.constrs in
    let ex = ex |> Ex.union d1.ex |> Ex.union d2.ex in
    domain ~constrs ex

  let remove ~ex c d =
    let constrs = TSet.remove c d.constrs in
    let ex = Ex.union ex d.ex in
    domain ~constrs ex

  let for_all f { constrs; _ } = TSet.for_all f constrs
end

let is_adt_ty = function
  | Ty.Tadt _ -> true
  | _ -> false

let is_adt r = is_adt_ty (X.type_info r)

module Domains = struct
  (** The type of simple domain maps. A domain map maps each representative
      (semantic value, of type [X.r]) to its associated domain. *)
  type t = {
    domains : Domain.t MX.t;
    (** Map from tracked representatives to their domain.

        We don't store domains for constructors and selectors. *)

    enums: SX.t;
    (** Set of tracked representatives whose the domain only contains
        enum constructors, that is constructors without payload.

        This field is used by the case split mechanism, see [pick_enum]. *)

    changed : SX.t;
    (** Representatives whose domain has changed since the last flush
        in [propagation]. *)
  }

  type _ Uf.id += Id : t Uf.id

  let pp ppf t =
    Fmt.(iter_bindings ~sep:semi MX.iter
           (box @@ pair ~sep:(any " ->@ ") X.print Domain.pp)
         |> braces
        )
      ppf t.domains

  let empty = { domains = MX.empty; enums = SX.empty; changed = SX.empty }

  let filter_ty = is_adt_ty

  (* TODO: This test is slow because we have to retrieve the list of
     destructors of the constructor [c] by searching in the list [cases].

     A better predicate will be easy to implement after getting rid of
     the legacy frontend and switching from [DE.t] to
     [Dolmen.Std.Expr.term_cst] to store the constructors. Indeed, [term_cst]
     contains the type of constructor and in particular its arity. *)
  let is_enum_constr r c =
    match X.type_info r with
    | Tadt (name, args) ->
      let cases = Ty.type_body name args in
      Compat.List.is_empty @@ Ty.assoc_destrs c cases
    | _ -> assert false

  let internal_update r nd t =
    let domains = MX.add r nd t.domains in
    let is_enum_domain = Domain.for_all (is_enum_constr r) nd in
    let enums = if is_enum_domain then SX.add r t.enums else t.enums in
    let changed = SX.add r t.changed in
    { domains; enums; changed }

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

  let init r t =
    match Th.embed r with
    | Alien _ when not (MX.mem r t.domains) ->
      (* We have to add a default domain if the key `r` is not in map in order
         to be sure that the case split mechanism will attempt to choose a
         value for it. *)
      let nd = Domain.unknown (X.type_info r) in
      internal_update r nd t
    | Alien _ | Constr _ | Select _ -> t

  (** [tighten r d t] replaces the domain of [r] in [t] by a domain [d]
      contained in the current domain of [r]. The representative [r] is marked
      [changed] after this call if the domain [d] is strictly smaller. *)
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
    let enums = SX.remove r t.enums in
    let changed = SX.remove r t.changed in
    { domains; enums; changed }

  exception Inconsistent = Domain.Inconsistent

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

    | exception Not_found -> init nr t

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

  let fold f t = MX.fold f t.domains

  let fold_enums f t = SX.fold f t.enums
end

let calc_destructor d e uf =
  let r, ex = Uf.find uf e in
  match Th.embed r with
  | Constr { c_args; _ } ->
    begin match My_list.assoc DE.Term.Const.equal d c_args with
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

let empty uf = {
  delayed = Rel_utils.Delayed.create ~is_ready dispatch;
  size_splits = Numbers.Q.one;
  new_terms = SE.empty;
}, Uf.GlobalDomains.add (module Domains) Domains.empty (Uf.domains uf)

(* ################################################################ *)
(*BISECT-IGNORE-BEGIN*)
module Debug = struct
  let assume l =
    Log.debug
      (fun k -> k "assume the literal:@ %a" (Xliteral.print_view X.print) l)
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

(* Update the domains of the semantic values [r1] and [r2] according to the
   disequality [r1 <> r2].

   This function alone is not sufficient to produce a complete decision
   procedure for the ADT theory. For instance, let's assume we have three
   semantic values [r1], [r2] and [r3] whose the domain is `{C1, C2}`. It's
   clear that `(distinct r1 r2 r3)` is unsatisfiable but we have not enough
   information to discover this contradiction.

   We plan to support model generation for ADT. As a by-product, we will got
   a complete decision procedure for the ADT through the case-split mechanism
   as we did in the Enum theory.

   @raise Domain.Inconsistent if the disequality is inconsistent with
          the current environment [env]. *)
let assume_distinct =
  let aux ~ex r1 r2 domains =
    match Th.embed r1 with
    | Constr { c_args; _ } when List.length c_args = 0 ->
      begin
        let d1 = Domains.get r1 domains in
        let d2 = Domains.get r2 domains in
        match Domain.as_singleton d1 with
        | Some (c, ex') ->
          let ex = Ex.union ex ex' in
          let nd = Domain.remove ~ex c d2 in
          Domains.tighten r2 nd domains
        | None -> domains
      end
    | _ ->
      (* If `d1` is a singleton domain but its constructor has a payload,
         we cannot tighten the domain of `r2` because they could have
         distinct payloads. *)
      domains
  in fun ~ex r1 r2 domains ->
    aux ~ex r1 r2 domains |> aux ~ex r2 r1

(* Assumes the tester `((_ is c) r)` where [r] can be a constructor
   application or a uninterpreted semantic value.

   @raise Domain.Inconsistent if we already know that the value of [r]
          cannot be an application of the constructor [c]. *)
let assume_is_constr ~ex r c domains =
  let d1 = Domains.get r domains in
  let d2 = Domain.singleton ~ex:Explanation.empty c in
  let nd = Domain.intersect ~ex d1 d2 in
  Domains.tighten r nd domains

(* Assume `(not ((_ is c) r))` where [r] can be a constructor application
   or a uninterpreted semantic value.

   We remove the destructor equations associated with [r] and [c].

   @raise Domain.Inconsistent if we already know that the value of [r] has to
          be an application of the constructor [c]. *)
let assume_not_is_constr ~ex r c domains =
  let d = Domains.get r domains in
  let nd = Domain.remove ~ex c d in
  Domains.tighten r nd domains

let add r uf domains =
  match X.type_info r with
  | Ty.Tadt _ ->
    Log.debug (fun k -> k "add %a" X.print r);
    let rr, _ = Uf.find_r uf r in
    Domains.init rr domains
  | _ ->
    domains

let add_rec r uf domains =
  List.fold_left (fun env lf -> add lf uf env) domains (X.leaves r)

let add env uf r t =
  if Options.get_disable_adts () then
    env, Uf.domains uf, []
  else
    let delayed, eqs = Rel_utils.Delayed.add env.delayed uf r t in
    { env with delayed }, Uf.domains uf, eqs

let assume_literals la uf domains =
  List.fold_left
    (fun domains lit ->
       let open Xliteral in
       match lit with
       | Distinct (false, [r1; r2]) as l, _, ex, _ when is_adt r2 ->
         Debug.assume l;
         let rr1, ex1 = Uf.find_r uf r1 in
         let rr2, ex2 = Uf.find_r uf r2 in
         (* The explanation [ex] explains why [r1] and [r2] are distinct,
            which is not sufficient to justify why [rr1] and [rr2] are
            distinct. *)
         let ex = Ex.union ex1 @@ Ex.union ex2 ex in
         (* Needed for models generation because fresh terms are not added with
            the function add. *)
         let env = add_rec rr1 uf domains in
         let env = add_rec rr2 uf env in
         assume_distinct ~ex rr1 rr2 env

       | Builtin (true, Sy.IsConstr c, [r]) as l, _, ex, _ ->
         Debug.assume l;
         let r, ex1 = Uf.find_r uf r in
         let ex = Ex.union ex1 ex in
         assume_is_constr ~ex r c domains

       | Builtin (false, Sy.IsConstr c, [r]) as l, _, ex, _ ->
         Debug.assume l;
         let r, ex1 = Uf.find_r uf r in
         let ex = Ex.union ex1 ex in
         assume_not_is_constr ~ex r c domains

       | _ -> domains
    ) domains la

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
        let cases = Ty.type_body name params in
        let ds =
          try Ty.assoc_destrs c cases with Not_found -> assert false
        in
        let xs = List.map (fun (_, ty) -> E.fresh_name ty) ds in
        let cons = E.mk_constr c xs ty in
        let r', ctx = X.make cons in
        (* In the current implementation of `X.make`, we produce
           a nonempty context only for interpreted semantic values
           of the `Arith` and `Records` theories. The semantic
           values `cons` never involves such values. *)
        assert (Compat.List.is_empty ctx);
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

let propagate_domains new_terms domains =
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
    ) ([], new_terms) domains

(* Update the counter of case split size in [env]. *)
let count_splits env la =
  List.fold_left
    (fun nb (_, _, _, i) ->
       match i with
       | Th_util.CS (Th_util.Th_adt, n) -> Numbers.Q.mult nb n
       | _ -> nb
    ) env.size_splits la

let assume env uf la =
  let ds = Uf.domains uf in
  let domains = Uf.GlobalDomains.find (module Domains) ds in
  Log.debug (fun k -> k "environment before assume:@ %a" Domains.pp domains);
  let delayed, result = Rel_utils.Delayed.assume env.delayed uf la in
  let domains =
    try
      assume_literals la uf domains
    with Domain.Inconsistent ex ->
      raise_notrace (Ex.Inconsistent (ex, Uf.cl_extract uf))
  in
  let (assume, new_terms), domains = propagate_domains env.new_terms domains in
  let assume = List.rev_append assume result.assume in
  let env = {
    delayed;
    size_splits = count_splits env la;
    new_terms;
  }
  in
  Log.debug (fun k -> k "environment after assume:@ %a" Domains.pp domains);
  env,
  Uf.GlobalDomains.add (module Domains) domains ds,
  Sig_rel.{ assume; remove = [] }

(* ################################################################ *)

let two = Numbers.Q.from_int 2

(* Find the constructor associated with the destructor [d] in the ADT [ty].

   requires: [d] is a destructor of [ty]. *)
(* TODO: we should compute this reverse map in `Ty` and store it there. *)
let constr_of_destr ty d =
  match ty with
  | Ty.Tadt (name, params) ->
    begin
      let cases = Ty.type_body name params in
      try
        let r =
          List.find
            (fun Ty.{ destrs; _ } ->
               List.exists (fun (d', _) -> DE.Term.Const.equal d d') destrs
            ) cases
        in
        r.constr
      with Not_found -> assert false
    end

  | _ -> assert false

exception Found of X.r * DE.term_cst

let can_split env n =
  let m = Options.get_max_split () in
  Numbers.Q.(compare (mult n env.size_splits) m) <= 0
  || Numbers.Q.sign m < 0

let (let*) = Option.bind

(* Do a case split by choosing a semantic value [r] and constructor [c]
   for which there are delayed destructor applications and propagate the
   literal [(not (_ is c) r)]. *)
let split_delayed_destructor env =
  if not @@ Options.get_enable_adts_cs () then
    None
  else
    try
      Rel_utils.Delayed.iter_delayed
        (fun r sy _e ->
           match sy with
           | Sy.Destruct destr -> raise_notrace @@ Found (r, destr)
           | _ -> ()
        ) env.delayed;
      None
    with Found (r, d) ->
      let c = constr_of_destr (X.type_info r) d in
      Some (LR.mkv_builtin false (Sy.IsConstr c) [r])

(* Pick a constructor in a tracked domain with minimal cardinal.
   Returns [None] if there is no such constructor. *)
let pick_best ds =
  Domains.fold
    (fun r d best ->
       let cd = Domain.cardinal d in
       match Th.embed r, best with
       | Constr _, _ -> best
       | _, Some (n, _, _) when n <= cd -> best
       | _ ->
         let c = Domain.choose d in
         Some (cd, r, c)
    ) ds None

(* Pick a constructor in a tracked domain whose the domain is of minimal
   cardinal among tracked domains of enum types. Returns [None] if there is no
   such constructor. *)
let pick_enum ds =
  Domains.fold_enums
    (fun r best ->
       let d = Domains.get r ds in
       let cd = Domain.cardinal d in
       match Th.embed r, best with
       | Constr _, _ -> best
       | _, Some (n, _, _) when n <= cd -> best
       | _ ->
         let c = Domain.choose d in
         Some (cd, r, c)
    ) ds None

let pick_domain ~for_model uf =
  let ds = Uf.(GlobalDomains.find (module Domains) @@ domains uf) in
  match pick_enum ds with
  | None when for_model -> pick_best ds
  | r -> r

let split_domain ~for_model env uf =
  let* cd, r, c = pick_domain ~for_model uf in
  if for_model || can_split env (Numbers.Q.from_int cd) then
    let _, cons = Option.get @@ build_constr_eq r c in
    let nr, ctx = X.make cons in
    (* In the current implementation of `X.make`, we produce
       a nonempty context only for interpreted semantic values
       of the `Arith` and `Records` theories. The semantic
       values `cons` never involves such values. *)
    assert (Compat.List.is_empty ctx);
    Some (LR.mkv_eq r nr)
  else
    None

let next_case_split ~for_model env uf =
  match split_delayed_destructor env with
  | None -> split_domain ~for_model env uf
  | r -> r

let case_split env uf ~for_model =
  if Options.get_disable_adts () then
    []
  else begin
    match next_case_split ~for_model env uf with
    | Some cs ->
      Log.debug
        (fun k -> k "environment before case split:@ %a"
            Domains.pp
            (Uf.GlobalDomains.find (module Domains) (Uf.domains uf)));
      Log.debug
        (fun k -> k "assume by case splitting:@ %a"
            (Xliteral.print_view X.print) cs);
      [ cs, true, Th_util.CS (Th_util.Th_adt, two)]
    | None ->
      Log.debug (fun k -> k "no case split done");
      []
  end

let optimizing_objective _env _uf _o = None

let query _env uf (ra, _, ex, _) =
  if Options.get_disable_adts () then None
  else
    let domains = Uf.GlobalDomains.find (module Domains) (Uf.domains uf) in
    try
      match ra with
      | Xliteral.Builtin(true, Sy.IsConstr c, [r]) ->
        let rr, _ = Uf.find_r uf r in
        ignore (assume_is_constr ~ex rr c domains);
        None

      | Xliteral.Builtin(false, Sy.IsConstr c, [r]) ->
        let rr, _ = Uf.find_r uf r in
        ignore (assume_not_is_constr ~ex rr c domains);
        None

      | _ ->
        None
    with
    | Domain.Inconsistent ex -> Some (ex, Uf.cl_extract uf)

(* ################################################################ *)
