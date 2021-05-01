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

type t =
  {
    classes : E.Set.t list;
    domains : (HSS.t * Explanation.t) MX.t;
    seen_destr : SE.t;
    seen_access : SE.t;
    seen_testers : HSS.t MX.t;
    [@ocaml.ppwarning "selectors should be improved. only representatives \
                       in it. No true or false _is"]

    selectors : (E.t * Ex.t) list MHs.t MX.t;
    size_splits : Numbers.Q.t;
    new_terms : SE.t;
    pending_deds :
      (r Sig_rel.literal * Ex.t * Th_util.lit_origin) list
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

  let print_env loc env =
    if Options.get_debug_adt () then begin
      print_dbg ~flushed:false ~module_name:"Adt_rel" ~function_name:"print_env"
        "@ @[<v 2>--ADT env %s ---------------------------------@ " loc;
      MX.iter
        (fun r (hss, ex) ->
           print_dbg ~flushed:false ~header:false
             "%a 's domain is " X.print r;
           begin
             match HSS.elements hss with
               []      -> ()
             | hs :: l ->
               print_dbg ~flushed:false ~header:false
                 "{ %s" (Hs.view hs);
               List.iter (fun hs ->
                   print_dbg ~flushed:false ~header:false
                     " | %s" (Hs.view hs)) l
           end;
           print_dbg ~flushed:false ~header:false " } %a@ " Ex.print ex;

        ) env.domains;
      print_dbg ~flushed:false ~header:false
        "@]@ @[<v 2>-- seen testers ---------------------------@ ";
      MX.iter
        (fun r hss ->
           HSS.iter
             (fun hs ->
                print_dbg ~flushed:false ~header:false
                  "(%a is %a)@ " X.print r Hs.print hs
             )hss
        )env.seen_testers;
      print_dbg ~flushed:false ~header:false
        "@]@ @[<v 2>-- selectors ------------------------------@ ";
      MX.iter
        (fun r mhs ->
           MHs.iter
             (fun hs l ->
                List.iter (fun (a, _) ->
                    print_dbg ~flushed:false ~header:false
                      "(%a is %a) ==> %a@ "
                      X.print r Hs.print hs E.print a
                  ) l
             )mhs
        )env.selectors;
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


let new_terms env = env.new_terms
let instantiate ~do_syntactic_matching:_ _ env _ _ = env, []

let assume_th_elt t th_elt _ =
  match th_elt.Expr.extends with
  | Util.Adt ->
    failwith "This Theory does not support theories extension"
  | _ -> t

let seen_tester r hs env =
  try HSS.mem hs (MX.find r env.seen_testers)
  with Not_found -> false


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
            let is_c = E.mk_builtin ~is_pos:true (Sy.IsConstr h) [t] in
            if Options.get_debug_adt () then
              Printer.print_dbg
                ~module_name:"Adt_rel"
                ~function_name:"deduce_is_constr"
                "%a" E.print is_c;
            (Sig_rel.LTerm is_c, ex, Th_util.Other) :: eqs
        in
        begin
          match E.term_view t with
          | { E.ty = Ty.Tadt (name,params) as ty; _ } ->
            (* Only do this deduction for finite types ??
                 may not terminate in some cases otherwise.
                 eg. type t = A of t
                 goal g: forall e,e' :t. e = C(e') -> false
                 + should not be guareded by "seen_tester"
            *)
            let cases = match Ty.type_body name params with
              | Ty.Adt cases -> cases
            in
            let {Ty.destrs; _} =
              try List.find (
                  fun { Ty.constr = c; _ } -> Hstring.equal h c
                ) cases
              with Not_found -> assert false
            in
            let xs = List.map (fun (_, ty) -> E.fresh_name ty) destrs in
            let cons = E.mk_term (Sy.constr (Hs.view h)) xs ty in
            let env = {env with new_terms = SE.add cons env.new_terms} in
            let eq = E.mk_eq t cons ~iff:false in
            if Options.get_debug_adt () then
              Printer.print_dbg
                ~module_name:"Adt_rel"
                ~function_name:"deduce equal to constr"
                "%a" E.print eq;
            let eqs = (Sig_rel.LTerm eq, ex, Th_util.Other) :: eqs in
            env, eqs
          | _ -> env, eqs
        end
      | _ ->
        Printer.print_err "%a" X.print r;
        assert false
    end
  | _ -> env,eqs

let values_of ty =
  match ty with
  | Ty.Tadt (name,params) ->
    let l = match Ty.type_body name params with
      | Ty.Adt cases -> cases
    in
    Some
      (List.fold_left (fun st {Ty.constr; _} -> HSS.add constr st) HSS.empty l)
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
        match values_of ty with None -> assert false | Some s -> s
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

let update_tester r hs env =
  let old = try MX.find r env.seen_testers with Not_found -> HSS.empty in
  {env with seen_testers = MX.add r (HSS.add hs old) env.seen_testers}

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
  let is_c = E.mk_builtin ~is_pos:true (Sy.IsConstr c) [e] in
  let eq = E.mk_eq access t ~iff:false in
  if Options.get_debug_adt () then
    Printer.print_dbg ~header:false
      "associated with constr %a@,%a => %a"
      Hstring.print c
      E.print is_c
      E.print eq;
  let r_e, ex_e = try Uf.find uf e with Not_found -> assert false in
  if trivial_tester r_e c then
    {env with pending_deds =
                (Sig_rel.LTerm eq, ex_e, Th_util.Other) :: env.pending_deds}
  else
  if seen_tester r_e c env then
    {env with pending_deds =
                (Sig_rel.LTerm eq, ex_e, Th_util.Other) :: env.pending_deds}
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
    | Sy.Op Sy.Destruct (hs, true), [e] -> (* guarded *)
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
      assert false (* not possible *)

    (*| Sy.Op Sy.IsConstr _, _ ->
      if get_debug_adt () then
      Printer.print_dbg
      "new Tester: %a" E.print t;
       { env with seen_testers = SE.add t env.seen_testers }
    *)
    | _ -> env

let add env (uf:uf) (r:r) t =
  add_aux env (uf:uf) (r:r) t, []


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

let add_diseq uf hss sm1 sm2 dep env eqs =
  match sm1, sm2 with
  | Adt.Alien r , Adt.Constr { c_name = h; c_args = []; _ }
  | Adt.Constr { c_name = h; c_args = []; _ }, Adt.Alien r  ->
    (* not correct with args *)
    let enum, ex =
      try MX.find r env.domains with Not_found -> hss, Ex.empty
    in
    let enum = HSS.remove h enum in
    let ex = Ex.union ex dep in
    if HSS.is_empty enum then raise (Ex.Inconsistent (ex, env.classes))
    else
      let env = { env with domains = MX.add r (enum, ex) env.domains } in
      if HSS.cardinal enum = 1 then
        let h' = HSS.choose enum in
        let env, eqs = deduce_is_constr uf r h' eqs env ex in
        env, eqs
      else env, eqs

  | Adt.Alien _ , Adt.Constr _ | Adt.Constr _, Adt.Alien _  ->
    env, eqs

  | Adt.Alien r1, Adt.Alien r2 ->
    let enum1,ex1=
      try MX.find r1 env.domains with Not_found -> hss,Ex.empty in
    let enum2,ex2=
      try MX.find r2 env.domains with Not_found -> hss,Ex.empty in

    let env, eqs =
      if HSS.cardinal enum1 = 1 then
        let ex = Ex.union dep ex1 in
        let h' = HSS.choose enum1 in
        deduce_is_constr uf r1 h' eqs env ex
      else env, eqs
    in
    let env, eqs =
      if HSS.cardinal enum2 = 1 then
        let ex = Ex.union dep ex2 in
        let h' = HSS.choose enum2 in
        deduce_is_constr uf r2 h' eqs env ex
      else env, eqs
    in
    env, eqs

  |  _ -> env, eqs

let assoc_and_remove_selector hs r env =
  try
    let mhs = MX.find r env.selectors in
    let deds = MHs.find hs mhs in
    let mhs = MHs.remove hs mhs in
    deds,
    (if MHs.is_empty mhs then {env with selectors = MX.remove r env.selectors}
     else {env with selectors = MX.add r mhs env.selectors})

  with Not_found ->
    [], env

let assume_is_constr uf hs r dep env eqs =
  match Th.embed r with
  | Adt.Constr{ c_name; _ } when not (Hs.equal c_name hs) ->
    raise (Ex.Inconsistent (dep, env.classes));
  | _ ->
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
             (Sig_rel.LTerm ded, Ex.union dep dep', Th_util.Other) :: eqs
          )eqs deds
      in
      let env = update_tester r hs env in

      let enum, ex =
        try MX.find r env.domains
        with Not_found ->
        (*Cannot just put assert false !
          some terms are not well inited *)
        match values_of (X.type_info r) with
        | None -> assert false
        | Some s -> s, Ex.empty
      in
      let ex = Ex.union ex dep in
      if not (HSS.mem hs enum) then raise (Ex.Inconsistent (ex, env.classes));
      let env, eqs = deduce_is_constr uf r hs eqs env ex in
      {env with domains = MX.add r (HSS.singleton hs, ex) env.domains} , eqs

let assume_not_is_constr uf hs r dep env eqs =
  match Th.embed r with
  | Adt.Constr{ c_name; _ } when Hs.equal c_name hs ->
    raise (Ex.Inconsistent (dep, env.classes));
  | _ ->

    let _, env = assoc_and_remove_selector hs r env in
    let enum, ex =
      try MX.find r env.domains with
        Not_found ->
        (* semantic values may be not inited with function add *)
        match values_of (X.type_info r) with
        | Some s -> s, Ex.empty
        | None -> assert false
    in
    if not (HSS.mem hs enum) then env, eqs
    else
      let enum = HSS.remove hs enum in
      let ex = Ex.union ex dep in
      if HSS.is_empty enum then raise (Ex.Inconsistent (ex, env.classes))
      else
        let env = { env with domains = MX.add r (enum, ex) env.domains } in
        if HSS.cardinal enum = 1 then
          let h' = HSS.choose enum in
          let env, eqs = deduce_is_constr uf r h' eqs env ex in
          env, eqs
        else env, eqs



(* dot it modulo equivalence class ? or is it sufficient ? *)
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
      | Some s -> { env with domains = MX.add r (s, Ex.empty) env.domains }
      | None ->
        env
    end
  | _ -> env

(* needed for models generation because fresh terms are not
   added with function add *)
let add_rec env r = List.fold_left add_aux env (X.leaves r)

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
                  eqs := (Sig_rel.LTerm a, dep, Th_util.Other) :: !eqs) l;
           end;
           let l = List.rev_map (fun (a, dep) -> a, Ex.union ex dep) l in
           MHs.add hs l mhs
        )old mhs
    in
    if Options.get_debug_adt () then
      Printer.print_dbg ~header:false "";
    { env with selectors = MX.add r2 _new env.selectors }, !eqs
  with Not_found -> env, eqs

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
      | Sig_rel.LTerm a -> Format.fprintf fmt "%a" E.print a;
      | _ -> assert false
    in
    if Options.get_debug_adt () then
      Printer.print_dbg ~module_name:"Adt_rel" ~function_name:"assume"
        "assume deduced %d equalities@ %a" (List.length eqs)
        (Printer.pp_list_no_space print) eqs;
    env, { Sig_rel.assume = eqs; remove = [] }


(* ################################################################ *)

let two = Numbers.Q.from_int 2

let case_split env _ ~for_model ~to_optimize =
  if to_optimize != None || Options.get_disable_adts () ||
     not (Options.get_enable_adts_cs())
  then
    Sig_rel.Split []
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
        (* cs on negative version would be better in general *)
        let cs =  LR.mkv_builtin false (Sy.IsConstr hs) [r] in
        Sig_rel.Split [ cs, true, Th_util.CS(Th_util.Th_adt, two) ]
      with Not_found ->
        Debug.no_case_split ();
        Sig_rel.Split []
    end

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
