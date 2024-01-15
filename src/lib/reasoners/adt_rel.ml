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
module Th = Shostak.Adt

type r = X.r
type uf = Uf.t

module Ex = Explanation
module E = Expr
module SE = E.Set
module Hs = Hstring
module HSS = Hs.Set
module Sy = Symbols

module MX = Shostak.MXH
module LR = Uf.LX
module SLR = Set.Make(LR)
module MHs = Hs.Map

let timer = Timers.M_Adt

type t =
  {
    classes : E.Set.t list;
    (* State of the union-find represented by all its equivalence classes.
       This state is kept for debugging purposes only. It is updated after
       assuming literals of the theory and returned by queries in case of
       inconsistency. *)

    domains : (HSS.t * Explanation.t) MX.t;
    (* Map of the uninterpreted semantic values to domains of their possible
       constructors. The explanation justifies that any value assigned to
       the semantic value has to use a constructor lying in the domain. *)

    (* TODO: rename this field. *)
    seen_destr : SE.t;
    (* Set of all the guarded destructors known by the theory. A guarded
       destructor isn't interpreted by the ADT theory.

       This field is used to prevent transforming twice a guarded
       destructor to its non-guarded version and for debugging purposes. *)

    (* TODO: rename this field. *)
    seen_access : SE.t;
    (* Set of all the non-guarded destructors known by the theory. Contrary
       to a guarded destructor, a non-guarded destructor is interpreted
       by the ADT theory. *)

    seen_testers : HSS.t MX.t;
    [@ocaml.ppwarning "selectors should be improved. only representatives \
                       in it. No true or false _is"]
    (* TODO: This code is outdated. It seems that the theory doesn't need
       to register all the testers in [add_aux]. Now this field is only
       read to remember we have already forced a constructor because we have
       assumed its associated tester. *)

    selectors : (E.t * Ex.t) list MHs.t MX.t;
    (* Map of pending destructor equations. A destructor equation on an
       ADT term [t] is an equation of the form:
         d t = d' t
       where [d] is a guarded destructor and [d'] its non-guarded version.

       More precisely, this map matches a class representative [r] with a map
       of constructors of the ADT type [X.type_info r] to a list of
       destructor equations of the form [d t = d' t] where [t] lies in the
       class of [r]. If a class representative changes, the structure is
       updated by [update_cs_modulo_eq].

       Consider [d] a guarded destructor and [c] its associated constructor.

       - When we register the destructor application [d t] in [add_aux], we
         produce an equation [d t = d' t] where [d'] is the non-guarded
         version of [d]. If we don't already know that the value of [t] has
         to use the constructor [c], we put the equation [d t = d' t] in this
         map. Otherwise we propagate the equation to CC(X).

       - When we assume a tester on [c] (see [assume_is_constr]), we retrieve
         and propagate to CC(X) all the pending destructor equations
         associated with the constructor [c]. *)

    size_splits : Numbers.Q.t;
    (* Product of the size of all the facts learnt by CS assumed in
       the theory.

       Currently this field is unused. *)

    new_terms : SE.t;
    (* Set of all the constructor applications built by the theory.
       See the function [deduce_is_constr]. *)

    (* TODO: rename this field. *)
    pending_deds :
      (r Sig_rel.literal * Ex.t * Th_util.lit_origin) list
      (* Pending queue of facts discovered by the theory. Facts are pending
         in the following situations:

         - The domain of a uninterpreted semantic value becomes a singleton.
           In this case, we deduce the constructor of the semantic value and
           we add this equation to the pending queue using [deduce_is_constr].

         - When we add a guarded destructor and we have already assumed the
           tester of its associated constructor, we add a new equation to the
           queue between this destructor and its unguarded version.

         This pending queue is flushed at the end of [assume] and its
         content is propagated to the environment of CC(X). *)
  }

let empty classes = {
  classes;
  domains = MX.empty;
  seen_destr = SE.empty;
  seen_access = SE.empty;
  seen_testers = MX.empty;
  selectors = MX.empty;
  size_splits = Numbers.Q.one;
  new_terms = SE.empty;
  pending_deds = [];
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
        " we assume %a" LR.print (LR.make a)

  let pp_testers ppf (r, ts) =
    let pp_tester ppf hs =
      Fmt.pf ppf "@[(%a is %a@])" X.print r Hstring.print hs
    in
    Fmt.(iter ~sep:cut HSS.iter pp_tester) ppf ts

  let pp_domain ppf (r, (hss, _ex)) =
    Fmt.pf ppf "@[The domain of %a is {%a@]}."
      X.print r
      Fmt.(iter ~sep:(const string "|") HSS.iter Hstring.print) hss

  let pp_selectors ppf (r, mhs) =
    let pp_selector ppf (hs, l) =
      let pp ppf (a, _) =
        Fmt.pf ppf "(%a is %a) ==> %a"
          X.print r
          Hstring.print hs
          E.print a
      in
      Fmt.(list ~sep:sp pp) ppf l
    in
    Fmt.iter_bindings MHs.iter pp_selector ppf mhs

  let print_env loc env =
    if Options.get_debug_adt () then begin
      print_dbg ~flushed:false ~module_name:"Adt_rel" ~function_name:"print_env"
        "@[<v 2>--ADT env %s ---------------------------------@ " loc;
      print_dbg ~flushed:false ~header:false "%a"
        Fmt.(iter_bindings ~sep:cut MX.iter pp_domain) env.domains;
      print_dbg ~flushed:false ~header:false
        "@]@ @[<v 2>-- seen testers ---------------------------@ ";
      print_dbg ~flushed:false ~header:false "%a"
        Fmt.(iter_bindings ~sep:cut MX.iter pp_testers) env.seen_testers;
      print_dbg ~flushed:false ~header:false
        "@]@ @[<v 2>-- selectors ------------------------------@ ";
      print_dbg ~flushed:false ~header:false "%a"
        Fmt.(iter_bindings ~sep:cut MX.iter pp_selectors) env.selectors;
      print_dbg ~header:false
        "@]@ -------------------------------------------";
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

let seen_tester r hs env =
  try HSS.mem hs (MX.find r env.seen_testers)
  with Not_found -> false

(* For a uninterpreted semantic value [r] and [h] a constructor of the form:
     (cons (d1 ty1) ... (dn tyn))
   this function adds the new equation to [eqs]:
     [t = cons x1 ... xn]
   where x1, ..., xn are fresh names of type respectively ty1, ..., tyn
   and [t] is the term associated with the uninterpreted semantic value [r].

   If the tester [(_ cons) t] hasn't been already seen, we also add it to
   the equations [eqs].

   Assume that [r] is a semantic value of type [Ty.Adt]. *)
let deduce_is_constr uf r h eqs env ex =
  let r, ex' = try Uf.find_r uf r with Not_found -> assert false in
  let ex = Ex.union ex ex' in
  match Th.embed r with
  | Adt.Alien r ->
    begin match X.term_extract r with
      | Some t, _ ->
        let eqs =
          if seen_tester r h env then eqs
          else
            let is_c = E.mk_tester (Hstring.view h) t in
            if Options.get_debug_adt () then
              Printer.print_dbg
                ~module_name:"Adt_rel"
                ~function_name:"deduce_is_constr"
                "%a" E.print is_c;
            (Literal.LTerm is_c, ex, Th_util.Other) :: eqs
        in
        begin
          match E.term_view t with
          | { E.ty = Ty.Tadt (name, params) as ty; _ } ->
            (* Only do this deduction for finite types ??
                 may not terminate in some cases otherwise.
                 eg. type t = A of t
                 goal g: forall e,e' :t. e = C(e') -> false
                 + should not be guareded by "seen_tester"
            *)
            let Ty.Adt cases = Ty.type_body name params in
            let destrs =
              try Ty.assoc_destrs h cases with Not_found -> assert false
            in
            let xs = List.map (fun (_, ty) -> E.fresh_name ty) destrs in
            let cons = E.mk_constr (Hstring.view h) xs ty in
            let env = {env with new_terms = SE.add cons env.new_terms} in
            let eq = E.mk_eq t cons ~iff:false in
            if Options.get_debug_adt () then
              Printer.print_dbg
                ~module_name:"Adt_rel"
                ~function_name:"deduce equal to constr"
                "%a" E.print eq;
            let eqs = (Literal.LTerm eq, ex, Th_util.Other) :: eqs in
            env, eqs
          | _ -> env, eqs
        end
      | _ ->
        Printer.print_err "%a" X.print r;
        assert false
    end
  | Constr _ | Select _ -> env, eqs

(* Collect all the constructors of the ADT type [ty]. *)
let values_of ty =
  match ty with
  | Ty.Tadt (name,params) ->
    let Ty.Adt cases = Ty.type_body name params in
    Some
      (List.fold_left (fun st {Ty.constr; _} -> HSS.add constr st)
         HSS.empty cases)
  | _ -> None

let add_adt env uf t r sy ty =
  if MX.mem r env.domains then env
  else
    match sy, ty with
    | Sy.Op Sy.Constr hs, Ty.Tadt _ ->
      if Options.get_debug_adt () then
        Printer.print_dbg
          ~module_name:"Adt_rel" ~function_name:"add_adt"
          "new ADT expr(C): %a" E.print t;
      { env with domains =
                   MX.add r (HSS.singleton hs, Ex.empty) env.domains }

    | _, Ty.Tadt _ ->
      if Options.get_debug_adt () then
        Printer.print_dbg
          ~module_name:"Adt_rel" ~function_name:"add_adt"
          "new ADT expr: %a" E.print t;
      let constrs =
        match values_of ty with
        | None ->
          (* The type [ty] is an ADT type. *)
          assert false
        | Some s -> s
      in
      let env =
        { env with domains = MX.add r (constrs, Ex.empty) env.domains }
      in
      if HSS.cardinal constrs = 1 then
        let h' = HSS.choose constrs in
        let env, pending_deds =
          deduce_is_constr uf r h' env.pending_deds env Ex.empty
        in
        {env with pending_deds}
      else
        env

    | _ -> env

(* Add the tester `((_ is hs) r)` to the environment [env]. *)
let update_tester r hs env =
  let old = try MX.find r env.seen_testers with Not_found -> HSS.empty in
  {env with seen_testers = MX.add r (HSS.add hs old) env.seen_testers}

(* Check if [((_ is hs) r)] is [true]. *)
let trivial_tester r hs =
  match Th.embed r with (* can filter further/better *)
  | Adt.Constr { c_name; _ } -> Hstring.equal c_name hs
  | _ -> false

let constr_of_destr ty dest =
  if Options.get_debug_adt () then
    Printer.print_dbg
      ~module_name:"Adt_rel" ~function_name:"constr_of_destr"
      "ty = %a" Ty.print ty;
  match ty with
  | Ty.Tadt (name, params) ->
    let cases =
      match Ty.type_body name params with
      | Ty.Adt cases -> cases
    in
    begin
      try
        List.find
          (fun {Ty.destrs; _} ->
             List.exists (fun (d, _) -> Hstring.equal dest d) destrs
          )cases
      with Not_found -> assert false (* invariant *)
    end
  | _ -> assert false


[@@ocaml.ppwarning "XXX improve. For each selector, store its \
                    corresponding constructor when typechecking ?"]
let add_guarded_destr env uf t hs e t_ty =
  if Options.get_debug_adt () then
    Printer.print_dbg ~flushed:false
      ~module_name:"Adt_rel" ~function_name:"add_guarded_destr"
      "new (guarded) Destr: %a@ " E.print t;
  let env = { env with seen_destr = SE.add t env.seen_destr } in
  let {Ty.constr = c; _} = constr_of_destr (E.type_info e) hs in
  let access = E.mk_term (Sy.destruct (Hs.view hs) ~guarded:false) [e] t_ty in
  (* XXX : Never add non-guarded access to list of new terms !
     This may/will introduce bugs when instantiating
     let env = {env with new_terms = SE.add access env.new_terms} in
  *)
  let is_c = E.mk_tester (Hstring.view c) e in
  let eq = E.mk_eq access t ~iff:false in
  if Options.get_debug_adt () then
    Printer.print_dbg ~header:false
      "associated with constr %a@,%a => %a"
      Hstring.print c
      E.print is_c
      E.print eq;
  let r_e, ex_e = try Uf.find uf e with Not_found -> assert false in
  if trivial_tester r_e c || seen_tester r_e c env then
    {env with pending_deds =
                (Literal.LTerm eq, ex_e, Th_util.Other) :: env.pending_deds}
  else
    let m_e = try MX.find r_e env.selectors with Not_found -> MHs.empty in
    let old = try MHs.find c m_e with Not_found -> [] in
    { env with selectors =
                 MX.add r_e (MHs.add c ((eq, ex_e)::old) m_e)
                   env.selectors }


[@@ocaml.ppwarning "working with X.term_extract r would be sufficient ?"]
let add_aux env (uf:uf) (r:r) t =
  if Options.get_disable_adts () then env
  else
    let { E.f = sy; xs; ty; _ } = E.term_view t in
    let env = add_adt env uf t r sy ty in
    match sy, xs with
    | Sy.Op Sy.Destruct (hs, true), [e] ->
      (* guarded *)
      if Options.get_debug_adt () then
        Printer.print_dbg
          ~module_name:"Adt_rel" ~function_name:"add_aux"
          "add guarded destruct: %a" E.print t;
      if (SE.mem t env.seen_destr) then env
      else add_guarded_destr env uf t hs e ty

    | Sy.Op Sy.Destruct (_, false), [_] ->
      (* not guarded *)
      if Options.get_debug_adt () then
        Printer.print_dbg
          ~module_name:"Adt_rel" ~function_name:"add_aux"
          "[ADTs] add unguarded destruct: %a" E.print t;
      { env with seen_access = SE.add t env.seen_access }

    | Sy.Op Sy.Destruct _, _ ->
      (* The arity of the [Sy.Destruct] operator is 1. *)
      assert false

    | _ -> env

let add env (uf:uf) (r:r) t =
  add_aux env (uf:uf) (r:r) t, []

(* Update the counter of case-split size in [env]. *)
let count_splits env la =
  let nb =
    List.fold_left
      (fun nb (_,_,_,i) ->
         match i with
         | Th_util.CS (Th_util.Th_sum, n) -> Numbers.Q.mult nb n
         | _ -> nb
      )env.size_splits la
  in
  {env with size_splits = nb}

(* Update the domains of the semantic values [sm1] and [sm2] according to
   the disequality [sm1 <> sm2>]. More precisely, if one of the semantic
   values is an application of a constructor [cons], we remove [cons] from
   the domain of the other one.

   In any case, we produce an equality if the domain of one of these semantic
   values becomes a singleton.

   @raise Ex.Inconsistent if the disequality is inconsistent with the
   current environment [env]. *)
let add_diseq uf hss sm1 sm2 dep env eqs =
  match sm1, sm2 with
  | Adt.Alien r , Adt.Constr { c_name = h; c_args = []; _ }
  | Adt.Constr { c_name = h; c_args = []; _ }, Adt.Alien r  ->
    let dom, ex =
      try MX.find r env.domains with Not_found -> hss, Ex.empty
    in
    let dom = HSS.remove h dom in
    let ex = Ex.union ex dep in
    if HSS.is_empty dom then raise (Ex.Inconsistent (ex, env.classes))
    else
      let env = { env with domains = MX.add r (dom, ex) env.domains } in
      if HSS.cardinal dom = 1 then
        let h' = HSS.choose dom in
        let env, eqs = deduce_is_constr uf r h' eqs env ex in
        env, eqs
      else env, eqs

  | Adt.Alien _ , Adt.Constr _ | Adt.Constr _, Adt.Alien _
  | Adt.Constr _, Adt.Constr _ ->
    (* Our implementation of the ADT theory is incomplete.
       See issue https://github.com/OCamlPro/alt-ergo/issues/1014. *)
    env, eqs

  | Adt.Alien r1, Adt.Alien r2 ->
    let dom1, ex1=
      try MX.find r1 env.domains with Not_found -> hss, Ex.empty in
    let dom2, ex2=
      try MX.find r2 env.domains with Not_found -> hss, Ex.empty in

    let env, eqs =
      if HSS.cardinal dom1 = 1 then
        let ex = Ex.union dep ex1 in
        let h' = HSS.choose dom1 in
        deduce_is_constr uf r1 h' eqs env ex
      else env, eqs
    in
    let env, eqs =
      if HSS.cardinal dom2 = 1 then
        let ex = Ex.union dep ex2 in
        let h' = HSS.choose dom2 in
        deduce_is_constr uf r2 h' eqs env ex
      else env, eqs
    in
    env, eqs

  |  _ -> env, eqs

(* Helper function used in [assume_is_constr] and [assume_not_is_constr].
   Retrieves the pending destructor equations associated with the semantic
   value [r] and the constructor [hs]. This function removes also these
   equations from [env.selectors]. *)
let assoc_and_remove_selector hs r env =
  try
    let mhs = MX.find r env.selectors in
    let deds = MHs.find hs mhs in
    let mhs = MHs.remove hs mhs in
    let env =
      if MHs.is_empty mhs then
        { env with selectors = MX.remove r env.selectors }
      else
        { env with selectors = MX.add r mhs env.selectors }
    in
    deds, env

  with Not_found ->
    [], env

(* Assumes the tester `((_ is hs) r)` where [r] can be a constructor
   application or a uninterpreted semantic value.

   We add the destructor equations associated with [r] and [hs] to [eqs].
   We also add the tester to [env.seen_testers].

   @raise Ex.Inconsistent if we already know that the value of [r]
          cannot be an application of the constructor [hs]. *)
let assume_is_constr uf hs r dep env eqs =
  match Th.embed r with
  | Adt.Constr { c_name; _ } when not (Hs.equal c_name hs) ->
    raise (Ex.Inconsistent (dep, env.classes));

  | Adt.Constr _ -> env, eqs

  | Adt.Select _ ->
    (* We never call this function on such semantic values. *)
    assert false

  | Adt.Alien _ ->
    if Options.get_debug_adt () then
      Printer.print_dbg
        ~module_name:"Adt_rel" ~function_name:"assume_is_constr"
        "assume is constr %a %a" X.print r Hs.print hs;
    if seen_tester r hs env then
      env, eqs
    else
      let deds, env = assoc_and_remove_selector hs r env in
      let eqs =
        List.fold_left
          (fun eqs (ded, dep') ->
             (Literal.LTerm ded, Ex.union dep dep', Th_util.Other) :: eqs
          )eqs deds
      in
      let env = update_tester r hs env in

      let dom, ex =
        try MX.find r env.domains
        with Not_found ->
        (* Cannot just put assert false! some terms are not well inited. *)
        match values_of (X.type_info r) with
        | None -> assert false
        | Some s -> s, Ex.empty
      in
      let ex = Ex.union ex dep in
      if not (HSS.mem hs dom) then raise (Ex.Inconsistent (ex, env.classes));
      let env, eqs = deduce_is_constr uf r hs eqs env ex in
      {env with domains = MX.add r (HSS.singleton hs, ex) env.domains}, eqs

(* Assume `(not ((_ is hs) r))` where [r] can be a constructor application
   or a uninterpreted semantic value.

   We remove the destructor equations associated with [r] and [hs].

   @raise Ex.Inconsistent if we already know that the value of [r] has to
          be an application of the constructor [hs]. *)
let assume_not_is_constr uf hs r dep env eqs =
  match Th.embed r with
  | Adt.Constr{ c_name; _ } when Hs.equal c_name hs ->
    raise (Ex.Inconsistent (dep, env.classes));
  | _ ->

    let _, env = assoc_and_remove_selector hs r env in
    let dom, ex =
      try MX.find r env.domains with
        Not_found ->
        (* Semantic values may be not inited with function add. *)
        match values_of (X.type_info r) with
        | Some s -> s, Ex.empty
        | None -> assert false
    in
    if not (HSS.mem hs dom) then env, eqs
    else
      let dom = HSS.remove hs dom in
      let ex = Ex.union ex dep in
      if HSS.is_empty dom then raise (Ex.Inconsistent (ex, env.classes))
      else
        let env = { env with domains = MX.add r (dom, ex) env.domains } in
        if HSS.cardinal dom = 1 then
          let h' = HSS.choose dom in
          let env, eqs = deduce_is_constr uf r h' eqs env ex in
          env, eqs
        else env, eqs



(* TODO: Do it modulo equivalence class ? or is it sufficient ? *)
(* Update the domains of the semantic values [sm1] and [sm2] according to
   the equation [sm1 = sm2]. More precisley, we replace their domains by
   their intersection.

   @raise Ex.Inconsistent if the domains of [sm1] and [sm2] are disjoint. *)
let add_eq uf hss sm1 sm2 dep env eqs =
  match sm1, sm2 with
  | Adt.Alien r, Adt.Constr { c_name = h; _ }
  | Adt.Constr { c_name = h; _ }, Adt.Alien r  ->
    let enum, ex =
      try MX.find r env.domains with Not_found -> hss, Ex.empty
    in
    let ex = Ex.union ex dep in
    if not (HSS.mem h enum) then raise (Ex.Inconsistent (ex, env.classes));
    let env, eqs = deduce_is_constr uf r h eqs env ex in
    {env with domains = MX.add r (HSS.singleton h, ex) env.domains} , eqs

  | Adt.Alien r1, Adt.Alien r2   ->
    let enum1,ex1 =
      try MX.find r1 env.domains with Not_found -> hss, Ex.empty in
    let enum2,ex2 =
      try MX.find r2 env.domains with Not_found -> hss, Ex.empty in
    let ex = Ex.union dep (Ex.union ex1 ex2) in
    let diff = HSS.inter enum1 enum2 in
    if HSS.is_empty diff then raise (Ex.Inconsistent (ex, env.classes));
    let domains = MX.add r1 (diff, ex) env.domains in
    let env = {env with domains = MX.add r2 (diff, ex) domains } in
    if HSS.cardinal diff = 1 then begin
      let h' = HSS.choose diff in
      let env, eqs = deduce_is_constr uf r1 h' eqs env ex in
      let env, eqs = deduce_is_constr uf r2 h' eqs env ex in
      env, eqs
    end
    else env, eqs

  |  _ -> env, eqs


let add_aux env r =
  Debug.add r;
  match Th.embed r with
  | Adt.Alien r when not (MX.mem r env.domains) ->
    begin match values_of (X.type_info r) with
      | Some s ->
        (* All the constructors are possible. *)
        { env with domains = MX.add r (s, Ex.empty) env.domains }
      | None ->
        env
    end
  | _ -> env

(* Needed for models generation because fresh terms are not
   added with function add. *)
let add_rec env r = List.fold_left add_aux env (X.leaves r)

(* Update the field [env.selectors] when a Subst equality have
   been propagated to CC(X).

   If [r2] becomes the class representative of [r1], this function is
   called and [env.selectors] maps [r2] to the union of the old
   selectors of [r2] and [r1]. *)
let update_cs_modulo_eq r1 r2 ex env eqs =
  (* PB Here: even if Subst, we are not sure that it was
     r1 |-> r2, because LR.mkv_eq may swap r1 and r2 *)
  try
    let old = MX.find r1 env.selectors in
    if Options.get_debug_adt () then
      Printer.print_dbg ~flushed:false
        ~module_name:"Adt_rel" ~function_name:"update_cs_modulo_eq"
        "update selectors modulo eq: %a |-> %a@ "
        X.print r1 X.print r2;
    let mhs = try MX.find r2 env.selectors with Not_found -> MHs.empty in
    let eqs = ref eqs in
    let _new =
      MHs.fold
        (fun hs l mhs ->
           if trivial_tester r2 hs then begin
             if Options.get_debug_adt () then
               Printer.print_dbg
                 ~flushed:false ~header:false
                 "make deduction because %a ? %a is trivial@ "
                 X.print r2 Hs.print hs;
             List.iter
               (fun (a, dep) ->
                  eqs := (Literal.LTerm a, dep, Th_util.Other) :: !eqs) l;
           end;
           let l = List.rev_map (fun (a, dep) -> a, Ex.union ex dep) l in
           MHs.add hs l mhs
        )old mhs
    in
    if Options.get_debug_adt () then
      Printer.print_dbg ~header:false "";
    { env with selectors = MX.add r2 _new env.selectors }, !eqs
  with Not_found -> env, eqs

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
    )la

let assume env uf la =
  if Options.get_disable_adts () then
    env, { Sig_rel.assume = []; remove = [] }
  else
    let la = remove_redundancies la in (* should be done globally in CCX *)
    let env = count_splits env la in
    let classes = Uf.cl_extract uf in
    let env = { env with classes = classes } in
    let aux bol r1 r2 dep env eqs = function
      | None     -> env, eqs
      | Some hss ->
        if bol then
          add_eq uf hss (Th.embed r1) (Th.embed r2) dep env eqs
        else
          add_diseq uf hss (Th.embed r1) (Th.embed r2) dep env eqs
    in
    Debug.print_env "before assume" env;
    let env, eqs =
      List.fold_left
        (fun (env,eqs) (a, b, c, d) ->
           Debug.assume a;
           match a, b, c, d with
           | Xliteral.Eq(r1,r2), _, ex, orig ->
             (* needed for models generation because fresh terms are not
                added with function add *)
             let env = add_rec (add_rec env r1) r2 in
             let env, eqs =
               if orig == Th_util.Subst then
                 update_cs_modulo_eq r1 r2 ex env eqs
               else
                 env, eqs
             in
             aux true  r1 r2 ex env eqs (values_of (X.type_info r1))

           | Xliteral.Distinct(false, [r1;r2]), _, ex, _ ->
             (* needed for models generation because fresh terms are not
                added with function add *)
             let env = add_rec (add_rec env r1) r2 in
             aux false r1 r2 ex env eqs (values_of (X.type_info r1))

           | Xliteral.Builtin(true, Sy.IsConstr hs, [e]), _, ex, _ ->
             assume_is_constr uf hs e ex env eqs

           | Xliteral.Builtin(false, Sy.IsConstr hs, [e]), _, ex, _
             [@ocaml.ppwarning "XXX: assume not (. ? .): reasoning missing ?"]
             ->
             assume_not_is_constr uf hs e ex env eqs

           | _ -> env, eqs

        ) (env,[]) la
    in
    let eqs = List.rev_append env.pending_deds eqs in
    let env = {env with pending_deds = []} in
    Debug.print_env "after assume" env;
    let print fmt (a,_,_) =
      match a with
      | Literal.LTerm a -> Format.fprintf fmt "%a" E.print a;
      | _ -> assert false
    in
    if Options.get_debug_adt () then
      Printer.print_dbg ~module_name:"Adt_rel" ~function_name:"assume"
        "assume deduced %d equalities@ %a" (List.length eqs)
        (Printer.pp_list_no_space print) eqs;
    env, { Sig_rel.assume = eqs; remove = [] }


(* ################################################################ *)

let two = Numbers.Q.from_int 2

(* Do a case-split by choosing a semantic value [r] and constructor [c]
   for which there are pending destructor equations and propagate the
   literal [(not (_ is c) r)]. *)
let case_split env _uf ~for_model =
  if Options.get_disable_adts () || not (Options.get_enable_adts_cs())
  then
    []
  else
    begin
      assert (not for_model);
      if Options.get_debug_adt () then Debug.print_env "before cs" env;
      try
        let r, mhs = MX.choose env.selectors in
        if Options.get_debug_adt () then
          Printer.print_dbg ~flushed:false
            ~module_name:"Adt_rel" ~function_name:"case_split"
            "found r = %a@ " X.print r;
        let hs, _ = MHs.choose mhs in
        if Options.get_debug_adt () then
          Printer.print_dbg ~header:false
            "found hs = %a" Hs.print hs;
        (* CS on negative version would be better in general. *)
        let cs =  LR.mkv_builtin false (Sy.IsConstr hs) [r] in
        [ cs, true, Th_util.CS (Th_util.Th_adt, two) ]
      with Not_found ->
        Debug.no_case_split ();
        []
    end

let optimizing_objective _env _uf _o = None

let query env uf (ra, _, ex, _) =
  if Options.get_disable_adts () then None
  else
    try
      match ra with
      | Xliteral.Builtin(true, Sy.IsConstr hs, [e]) ->
        ignore (assume_is_constr uf hs e ex env []);
        None

      | Xliteral.Builtin(false, Sy.IsConstr hs, [e])
        [@ocaml.ppwarning "XXX: assume not (. ? .): reasoning missing ?"]
        ->
        ignore (assume_not_is_constr uf hs e ex env []);
        None
      | _ ->
        None
    with
    | Ex.Inconsistent (expl, classes) -> Some (expl, classes)

(* ################################################################ *)
