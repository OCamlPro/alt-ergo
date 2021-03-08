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
open Sig

module X = Shostak.Combine

module Ac = Shostak.Ac
module Ex = Explanation

module Sy = Symbols
module E = Expr
module ME = Expr.Map
module SE = Expr.Set

module LX =
  Xliteral.Make(struct type t = X.r let compare = X.hash_cmp include X end)
module MapL = Emap.Make(LX)

module MapX = struct
  include Shostak.MXH
  let find m x = Steps.incr (Steps.Uf); find m x
end
module SetX = Shostak.SXH

module SetXX = Set.Make(struct
    type t = X.r * X.r
    let compare (r1, r1') (r2, r2') =
      let c = X.hash_cmp r1 r2 in
      if c <> 0 then c
      else  X.hash_cmp r1' r2'
  end)

module SetAc = Set.Make(struct type t = Ac.t let compare = Ac.compare end)

module SetRL = Set.Make
    (struct
      type t = Ac.t * X.r * Ex.t
      let compare (ac1,_,_) (ac2,_,_)= Ac.compare ac1 ac2
    end)

module RS = struct
  include Map.Make(struct type t = Sy.t let compare = Sy.compare end)

  let find k m =
    try find k m with Not_found -> SetRL.empty

  let add_rule (({ h ; _ }, _, _) as rul) mp =
    add h (SetRL.add rul (find h mp)) mp

  let remove_rule (({ h ; _ }, _, _) as rul) mp =
    add h (SetRL.remove rul (find h mp)) mp

end

type r = X.r

type t = {

  (* term -> [t] *)
  make : r ME.t;

  (* representative table *)
  repr : (r * Ex.t) MapX.t;

  (* r -> class (of terms) *)
  classes : SE.t MapX.t;

  (*associates each value r with the set of semantical values whose
    representatives contains r *)
  gamma : SetX.t MapX.t;

  (* the disequations map *)
  neqs: Ex.t MapL.t MapX.t;

  (*AC rewrite system *)
  ac_rs : SetRL.t RS.t;
}


exception Found_term of E.t

(* hack: would need an inverse map from semantic values to terms *)
let terms_of_distinct env l = match LX.view l with
  | Xliteral.Distinct (false, rl) ->
    let lt =
      List.fold_left (fun acc r ->
          try
            let cl = MapX.find r env.classes in
            SE.iter (fun t ->
                if X.equal (ME.find t env.make) r then
                  raise (Found_term t)) cl;
            acc
          with
          | Found_term t -> t :: acc
          | Not_found -> acc) [] rl
    in
    let rec distrib = function
      | x :: r -> (distrib r) @
                  (List.map (fun y -> SE.add x (SE.singleton y)) r)
      | [] -> []
    in
    distrib lt

  | _ -> assert false


let cl_extract env =
  if get_bottom_classes () then
    let classes = MapX.fold (fun _ cl acc -> cl :: acc) env.classes [] in
    MapX.fold (fun _ ml acc ->
        MapL.fold (fun l _ acc -> (terms_of_distinct env l) @ acc) ml acc
      ) env.neqs classes
  else []


(*BISECT-IGNORE-BEGIN*)
module Debug = struct
  open Printer

  (* unused --
     let rs_print fmt = SetX.iter (fprintf fmt "\t%a@." X.print)
  *)

  let lm_print fmt =
    MapL.iter (fun k dep -> fprintf fmt "%a %a" LX.print k Ex.print dep)

  let pmake fmt m =
    fprintf fmt "@[<v 2>map:@,";
    ME.iter (fun t r -> fprintf fmt "%a -> %a@," E.print t X.print r) m;
    fprintf fmt "@]@,"

  let prepr fmt m =
    fprintf fmt
      "@[<v 2>------------- UF: Representatives map ----------------@,";
    MapX.iter
      (fun r (rr,dep) ->
         fprintf fmt "%a --> %a %a@," X.print r X.print rr Ex.print dep) m;
    fprintf fmt "@]@,"

  let prules fmt s =
    fprintf fmt
      "@[<v 2>------------- UF: AC rewrite rules ----------------------@,";
    RS.iter
      (fun _ srl ->
         SetRL.iter
           (fun (ac,d,dep)-> fprintf fmt "%a ~~> %a %a@,"
               X.print (X.ac_embed ac) X.print d Ex.print dep
           )srl
      )s;
    fprintf fmt "@]@,"

  let pclasses fmt m =
    fprintf fmt
      "@[<v 2>------------- UF: Class map --------------------------@,";
    MapX.iter
      (fun k s -> fprintf fmt "%a -> %a@," X.print k E.print_list
          (SE.elements s)) m;
    fprintf fmt "@]@,"

  (* unused --
     let pgamma fmt m =
     fprintf fmt "------------- UF: Gamma map --------------------------@.";
     MapX.iter (fun k s -> fprintf fmt "%a -> \n%a" X.print k rs_print s) m
  *)

  let pneqs fmt m =
    fprintf fmt
      "@[<v 2>------------- UF: Disequations map--------------------@ ";
    MapX.iter (fun k s -> fprintf fmt "%a -> %a@ " X.print k lm_print s) m;
    fprintf fmt "@]@ "

  let all env =
    if get_debug_uf () then
      print_dbg
        ~module_name:"Uf" ~function_name:"all"
        "@[<v 0>-------------------------------------------------@ \
         %a%a%a%a%a\
         -------------------------------------------------@]"
        pmake env.make
        prepr env.repr
        prules env.ac_rs
        pclasses env.classes
        pneqs env.neqs

  let lookup_not_found t env =
    print_err
      "Uf: %a Not_found in env" E.print t;
    all env


  let canon_of r rr =
    if get_rewriting () && get_verbose () then
      print_dbg "canon %a = %a" X.print r X.print rr

  let init_leaf p =
    if get_debug_uf () then
      print_dbg
        ~module_name:"Uf" ~function_name:"init_leaf"
        "init leaf : %a" X.print p

  let critical_pair rx ry =
    if get_debug_uf () then
      print_dbg
        ~module_name:"Uf" ~function_name:"critical_pair"
        "critical pair : %a = %a@." X.print rx X.print ry

  let collapse_mult g2 d2 =
    if get_debug_ac () then
      print_dbg
        ~module_name:"Uf" ~function_name:"collapse_mult"
        "collapse *: %a = %a"
        X.print g2 X.print d2

  let collapse g2 d2 =
    if get_debug_ac () then
      print_dbg
        ~module_name:"Uf" ~function_name:"collapse"
        "collapse: %a = %a"
        X.print g2 X.print d2

  let compose p v g d =
    if get_debug_ac () then
      print_dbg
        ~module_name:"Uf" ~function_name:"compose"
        "compose : %a -> %a on %a and %a"
        X.print p X.print v
        Ac.print g X.print d

  let x_solve rr1 rr2 dep =
    if get_debug_uf () then
      print_dbg
        ~module_name:"Uf" ~function_name:"x_solve"
        "x-solve: %a = %a %a"
        X.print rr1 X.print rr2 Ex.print dep

  let ac_solve p v dep =
    if get_debug_uf () then
      print_dbg
        ~module_name:"Uf" ~function_name:"ac_solve"
        "ac-solve: %a |-> %a %a"
        X.print p X.print v Ex.print dep

  let ac_x r1 r2 =
    if get_debug_uf () then
      print_dbg
        ~module_name:"Uf" ~function_name:"ac_x"
        "ac(x): delta (%a) = delta (%a)"
        X.print r1 X.print r2

  let distinct d =
    if get_debug_uf () then
      print_dbg
        ~module_name:"Uf" ~function_name:"distinct"
        "distinct %a" LX.print d

  let are_distinct t1 t2 =
    if get_debug_uf () then
      print_dbg
        ~module_name:"Uf" ~function_name:"are_distinct"
        "are_distinct %a %a" E.print t1 E.print t2


  let check_inv_repr_normalized =
    let trace orig =
      print_err
        "[uf.%s] invariant broken when calling check_inv_repr_normalized"
        orig
    in
    fun orig repr ->
      MapX.iter
        (fun _ (rr, _) ->
           List.iter
             (fun x ->
                try
                  if not (X.equal x (fst (MapX.find x repr))) then
                    let () = trace orig in
                    assert false
                with Not_found ->
                  (* all leaves that are in normal form should be in repr ?
                     not AC leaves, which can be created dynamically,
                     not for other, that can be introduced by make and solve*)
                  ()
             )(X.leaves rr)
        )repr

  let check_invariants orig env =
    if Options.get_enable_assertions() then begin
      check_inv_repr_normalized orig env.repr;
    end
end
(*BISECT-IGNORE-END*)

module Env = struct

  let mem env t = ME.mem t env.make

  let lookup_by_t t env =
    Options.exec_thread_yield ();
    try MapX.find (ME.find t env.make) env.repr
    with Not_found ->
      Debug.lookup_not_found t env;
      assert false (*X.make t, Ex.empty*) (* XXXX *)

  let lookup_by_t___without_failure t env =
    try MapX.find (ME.find t env.make) env.repr
    with Not_found -> fst (X.make t), Ex.empty

  let lookup_by_r r env =
    Options.exec_thread_yield ();
    try MapX.find r env.repr with Not_found -> r, Ex.empty

  let disjoint_union l_1 l_2 =
    let rec di_un (l1,c,l2) (l_1,l_2)=
      Options.exec_thread_yield ();
      match l_1,l_2 with
      | [],[] -> l1, c, l2
      | l, [] -> di_un (l @ l1,c,l2) ([],[])
      | [], l -> di_un (l1,c,l @ l2) ([],[])
      | (a,m)::r, (b,n)::s ->
        let cmp = X.str_cmp a b in
        if cmp = 0 then
          if m = n then di_un (l1,(a,m)::c,l2) (r,s)
          else if m > n then di_un ((a,m-n)::l1,(a,n)::c,l2) (r,s)
          else di_un (l1,(b,n)::c,(b,n-m)::l2) (r,s)
        else if cmp > 0 then di_un ((a,m)::l1,c,l2) (r,(b,n)::s)
        else di_un (l1,c,(b,n)::l2) ((a,m)::r,s)
    in di_un ([],[],[]) (l_1,l_2)


  (* Debut : Code pour la mise en forme normale modulo env *)
  exception List_minus_exn
  let list_minus l_1 l_2 =
    let rec di_un l1 l_1 l_2 =
      match l_1, l_2 with
        [],[] -> l1
      | l, [] -> l @ l1
      | [], _ -> raise List_minus_exn
      | (a,m)::r, (b,n)::s ->
        let cmp = X.str_cmp a b in
        if cmp = 0 then
          if m = n then di_un l1 r s
          else if m > n then di_un ((a,m-n)::l1) r s
          else raise List_minus_exn
        else if cmp > 0 then di_un ((a,m)::l1) r ((b,n)::s)
        else raise List_minus_exn
    in di_un [] l_1 l_2

  let apply_rs r rls =
    let fp = ref true in
    let r = ref r in
    let ex = ref Ex.empty in
    let rec apply_rule ((p, v, dep) as rul) =
      let c = Ac.compare !r p in
      if c = 0 then begin
        r := {!r with l=[v, 1]};
        ex := Ex.union !ex dep
      end
      else if c < 0 then raise Exit
      else
        try
          r := {!r with l = Ac.add !r.h (v, 1) (list_minus !r.l p.l)};
          ex := Ex.union !ex dep;
          fp := false;
          apply_rule rul
        with List_minus_exn -> ()
    in
    let rec fixpoint () =
      Options.exec_thread_yield ();
      (try SetRL.iter apply_rule rls with Exit -> ());
      if !fp then !r, !ex else (fp := true; fixpoint ())
    in fixpoint()

  let filter_leaves r =
    List.fold_left
      (fun (p,q) r -> match X.ac_extract r with
         | None    -> SetX.add r p, q
         | Some ac -> p, SetAc.add ac q
      )(SetX.empty,SetAc.empty) (X.leaves r)

  let canon_empty st env =
    SetX.fold
      (fun p ((z, ex) as acc) ->
         let q, ex_q = lookup_by_r p env in
         if X.equal p q then acc else (p,q)::z, Ex.union ex_q ex)
      st ([], Ex.empty)

  let canon_ac st env =
    SetAc.fold
      (fun ac (z,ex) ->
         let rac, ex_ac = apply_rs ac (RS.find ac.h env.ac_rs) in
         if Ac.compare ac rac = 0 then z, ex
         else (X.color ac, X.color rac) :: z, Ex.union ex ex_ac)
      st ([], Ex.empty)

  let canon_aux rx = List.fold_left (fun r (p,v) -> X.subst p v r) rx

  let rec canon env r ex_r =
    let se, sac = filter_leaves r in
    let subst, ex_subst = canon_empty se env in
    let subst_ac, ex_ac = canon_ac sac env in (* explications? *)
    let r2 = canon_aux (canon_aux r subst_ac) subst in
    let ex_r2 = Ex.union (Ex.union ex_r ex_subst) ex_ac in
    if X.equal r r2 then r2, ex_r2 else canon env r2 ex_r2

  let normal_form env r =
    let rr, ex = canon env r Ex.empty in
    Debug.canon_of r rr;
    rr,ex

  (* Fin : Code pour la mise en forme normale modulo env *)

  let find_or_normal_form env r =
    Options.exec_thread_yield ();
    try MapX.find r env.repr with Not_found -> normal_form env r

  let lookup_for_neqs env r =
    Options.exec_thread_yield ();
    try MapX.find r env.neqs with Not_found -> MapL.empty

  let add_to_classes t r classes =
    MapX.add r
      (SE.add t (try MapX.find r classes with Not_found -> SE.empty))
      classes

  let update_classes c nc classes =
    let s1 = try MapX.find c classes with Not_found -> SE.empty in
    let s2 = try MapX.find nc classes with Not_found -> SE.empty in
    MapX.add nc (SE.union s1 s2) (MapX.remove c classes)

  let add_to_gamma r c gamma =
    Options.exec_thread_yield ();
    List.fold_left
      (fun gamma x ->
         let s = try MapX.find x gamma with Not_found -> SetX.empty in
         MapX.add x (SetX.add r s) gamma) gamma (X.leaves c)

  let explain_repr_of_distinct x repr_x dep lit env =
    match LX.view lit with
    | Xliteral.Distinct (false, ([_;_] as args)) ->
      List.fold_left
        (fun dep r -> Ex.union dep (snd (find_or_normal_form env r)))
        dep args

    | Xliteral.Pred (r, _) ->
      Ex.union dep (snd (find_or_normal_form env r))

    | Xliteral.Distinct (false, l) ->
      List.fold_left
        (fun d r ->
           let z, ex = find_or_normal_form env r in
           if X.equal z x || X.equal z repr_x then Ex.union d ex else d
        )dep l

    | _ -> assert false

  (* r1 = r2 => neqs(r1) \uplus neqs(r2) *)
  let update_neqs x repr_x dep env =
    let merge_disjoint_maps l1 ex1 mapl =
      try
        let ex2 = MapL.find l1 mapl in
        Options.tool_req 3 "TR-CCX-Congruence-Conflict";
        let ex = Ex.union (Ex.union ex1 ex2) dep in
        let ex = explain_repr_of_distinct x repr_x ex l1 env in
        raise (Ex.Inconsistent (ex, cl_extract env))
      with Not_found ->
        (* with the use of explain_repr_of_distinct above, I
           don't need to propagate dep to ex1 here *)
        MapL.add l1 ex1 mapl
    in
    let nq_r1 = lookup_for_neqs env x in
    let nq_r2 = lookup_for_neqs env repr_x in
    let small, big =
      if MapL.height nq_r1 < MapL.height nq_r2 then nq_r1, nq_r2
      else nq_r2, nq_r1
    in
    let mapl = MapL.fold merge_disjoint_maps small big in
    (* remove x from the map to avoid eventual bugs if call this
       function again with x == repr_x *)
    MapX.add repr_x mapl (MapX.remove x env.neqs)

  let init_leaf env p =
    Debug.init_leaf p;
    let in_repr = MapX.mem p env.repr in
    let rp, ex_rp =
      if in_repr then MapX.find p env.repr
      else normal_form env p
    in
    let mk_env = env.make in
    let make =
      match X.term_extract p with
      | Some t, true when not (ME.mem t mk_env) -> ME.add t p mk_env
      | _ -> mk_env
    in
    let env =
      { env with
        make    = make;
        repr    =
          if in_repr then env.repr
          else MapX.add p (rp, ex_rp) env.repr;
        classes =
          if MapX.mem p env.classes then env.classes
          else update_classes p rp env.classes;
        gamma   =
          if in_repr then env.gamma
          else add_to_gamma p rp env.gamma ;
        neqs    =
          if MapX.mem p env.neqs then env.neqs
          else update_neqs p rp Ex.empty env }
    in
    Debug.check_invariants "init_leaf" env;
    env

  let init_leaves env v =
    let env = List.fold_left init_leaf env (X.leaves v) in
    init_leaf env v

  let init_new_ac_leaves env mkr =
    List.fold_left
      (fun env x ->
         match X.ac_extract x with
         | None -> env
         | Some _ ->
           if MapX.mem x env.repr then env
           else init_leaves env x
      ) env (X.leaves mkr)

  let init_term env t =
    let mkr, ctx = X.make t in
    let rp, ex = normal_form env mkr in
    let env =
      {env with
       make    = ME.add t mkr env.make;
       repr    = MapX.add mkr (rp,ex) env.repr;
       classes = add_to_classes t rp env.classes;
       gamma   = add_to_gamma mkr rp env.gamma;
       neqs    =
         if MapX.mem rp env.neqs then env.neqs (* pourquoi ce test *)
         else MapX.add rp MapL.empty env.neqs}
    in
    (init_new_ac_leaves env mkr), ctx

  let head_cp eqs env pac ({ h ; _ } as ac) v dep =
    try (*if RS.mem h env.ac_rs then*)
      SetRL.iter
        (fun (g, d, dep_rl) ->
           if X.equal pac (X.ac_embed g) && X.equal v d then ()
           else
             match disjoint_union ac.l g.l with
             | _  , [] , _  -> ()
             | l1 , _cm , l2 ->
               let rx = X.color {ac with l = Ac.add h (d,1) l1} in
               let ry = X.color {g  with l = Ac.add h (v,1) l2} in
               Debug.critical_pair rx ry;
               if not (X.equal rx ry) then
                 Queue.push (rx, ry, Ex.union dep dep_rl) eqs)
        (RS.find h env.ac_rs)
    with Not_found -> assert false

  let comp_collapse eqs env (p, v, dep) =
    RS.fold
      (fun _ rls env ->
         SetRL.fold
           (fun ((g, d, dep_rl) as rul) env ->
              Options.exec_thread_yield ();
              Steps.incr Steps.Ac;
              let env = {env with ac_rs = RS.remove_rule rul env.ac_rs} in
              let gx = X.color g in
              let g2, ex_g2 = normal_form env (Ac.subst p v g) in
              let d2, ex_d2 = normal_form env (X.subst p v d) in
              if X.str_cmp g2 d2 <= 0 then begin
                Debug.collapse_mult g2 d2;
                let ex = Ex.union
                    (Ex.union ex_g2 ex_d2) (Ex.union dep_rl dep) in
                Queue.push (g2, d2, ex) eqs;
                env
              end
              else
              if X.equal g2 gx then (* compose *)
                begin
                  Debug.compose p v g d;
                  let ex = Ex.union ex_d2 (Ex.union dep_rl dep) in
                  {env with ac_rs = RS.add_rule (g,d2, ex) env.ac_rs}
                end
              else (* collapse *)
                begin
                  Debug.collapse g2 d2;
                  let ex =
                    Ex.union
                      (Ex.union ex_g2 ex_d2) (Ex.union dep_rl dep) in
                  Queue.push (g2, d2, ex) eqs;
                  env
                end
           ) rls env
      ) env.ac_rs env

  (* TODO explications: ajout de dep dans ac_rs *)
  let apply_sigma_ac eqs env ((p, v, dep) as sigma) =
    match X.ac_extract p with
    | None ->
      comp_collapse eqs env sigma
    | Some r ->
      let env = {env with ac_rs = RS.add_rule (r, v, dep) env.ac_rs} in
      let env = comp_collapse eqs env sigma in
      head_cp eqs env p r v dep;
      env

  let update_aux dep set env=
    SetXX.fold
      (fun (rr, nrr) env ->
         { env with
           neqs = update_neqs rr nrr dep env ;
           classes = update_classes rr nrr env.classes})
      set env

  (* Patch modudo AC for CC: if p is a leaf different from r and r is AC
     and reduced by p, then r --> nrr should be added as a PIVOT, not just
     as TOUCHED by p |-> ... This is required for a correct update of USE *)
  let update_global_tch global_tch p r nrr ex =
    if X.equal p r then global_tch
    else
      match X.ac_extract r with
      | None   -> global_tch
      | Some _ -> (r, [r, nrr, ex], nrr) :: global_tch


  let apply_sigma_uf env (p, v, dep) global_tch =
    assert (MapX.mem p env.gamma);
    let use_p = MapX.find p env.gamma in
    try
      let env, touched_p, global_tch, neqs_to_up =
        SetX.fold
          (fun r ((env, touched_p, global_tch, neqs_to_up) as acc) ->
             Options.exec_thread_yield ();
             let rr, ex = MapX.find r env.repr in
             let nrr = X.subst p v rr in
             if X.equal rr nrr then acc
             else
               let ex  = Ex.union ex dep in
               let env =
                 {env with
                  repr = MapX.add r (nrr, ex) env .repr;
                  gamma = add_to_gamma r nrr env.gamma }
               in
               env,
               (r, nrr, ex)::touched_p,
               update_global_tch global_tch p r nrr ex,
               SetXX.add (rr, nrr) neqs_to_up
          ) use_p (env, [], global_tch, SetXX.empty)
      in
      (* Correction : Do not update neqs twice for the same r *)
      update_aux dep neqs_to_up env, touched_p, global_tch

    with Not_found -> assert false

  let up_uf_rs dep env tch =
    if RS.is_empty env.ac_rs then env, tch
    else
      let env, tch, neqs_to_up = MapX.fold
          (fun r (rr,ex) ((env, tch, neqs_to_up) as acc) ->
             Options.exec_thread_yield ();
             let nrr, ex_nrr = normal_form env rr in
             if X.equal nrr rr then acc
             else
               let ex = Ex.union ex ex_nrr in
               let env =
                 {env with
                  repr = MapX.add r (nrr, ex) env.repr;
                  gamma = add_to_gamma r nrr env.gamma }
               in
               let tch =
                 if X.is_a_leaf r then (r,[r, nrr, ex],nrr) :: tch
                 else tch
               in
               env, tch, SetXX.add (rr, nrr) neqs_to_up
          ) env.repr (env, tch, SetXX.empty)
      in
      (* Correction : Do not update neqs twice for the same r *)
      update_aux dep neqs_to_up env, tch

  let apply_sigma eqs env tch ((p, v, dep) as sigma) =
    let env = init_leaves env p in
    let env = init_leaves env v in
    let env = apply_sigma_ac eqs env sigma in
    let env, touched_sigma, tch = apply_sigma_uf env sigma tch in
    up_uf_rs dep env ((p, touched_sigma, v) :: tch)

end

let add env t =
  Options.tool_req 3 "TR-UFX-Add";
  if ME.mem t env.make then env, []
  else
    let env, l = Env.init_term env t in
    Debug.check_invariants "add" env;
    env, l

let ac_solve eqs dep (env, tch) (p, v) =
  Debug.ac_solve p v dep;
  let rv, ex_rv = Env.find_or_normal_form env v in
  if not (X.equal v rv) then begin
    (* v is not in normal form ==> replay *)
    Queue.push (p, rv, Ex.union dep ex_rv) eqs;
    env, tch
  end
  else
    let rp, ex_rp = Env.find_or_normal_form env p in
    if not (X.equal p rp) then begin
      (* p is not in normal form ==> replay *)
      Queue.push (rp, v, Ex.union dep ex_rp) eqs;
      env, tch
    end
    else
      (* both p and v are in normal form ==> apply subst p |-> v *)
      Env.apply_sigma eqs env tch (p, v, dep)

let x_solve env r1 r2 dep =
  let rr1, ex_r1 = Env.find_or_normal_form env r1 in
  let rr2, ex_r2 = Env.find_or_normal_form env r2 in
  let dep = Ex.union dep (Ex.union ex_r1 ex_r2) in
  Debug.x_solve rr1 rr2 dep;
  if X.equal rr1 rr2 then begin
    Options.tool_req 3 "TR-CCX-Remove";
    [], dep (* Remove rule *)
  end
  else
    begin
      ignore (Env.update_neqs rr1 rr2 dep env);
      try X.solve rr1 rr2, dep
      with Util.Unsolvable ->
        Options.tool_req 3 "TR-CCX-Congruence-Conflict";
        raise (Ex.Inconsistent (dep, cl_extract env))
    end

let rec ac_x eqs env tch =
  if Queue.is_empty eqs then env, tch
  else
    let r1, r2, dep = Queue.pop eqs in
    Debug.ac_x r1 r2;
    let sbs, dep = x_solve env r1 r2 dep in
    let env, tch = List.fold_left (ac_solve eqs dep) (env, tch) sbs in
    if get_debug_uf () then Debug.all env;
    ac_x eqs env tch

let union env r1 r2 dep =
  Options.tool_req 3 "TR-UFX-Union";
  let equations = Queue.create () in
  Queue.push (r1,r2, dep) equations;
  let env, res = ac_x equations env [] in
  Debug.check_invariants "union" env;
  env, res

let union env r1 r2 dep =
  if Options.get_timers() then
    try
      Timers.exec_timer_start Timers.M_UF Timers.F_union;
      let res = union env r1 r2 dep in
      Timers.exec_timer_pause Timers.M_UF Timers.F_union;
      res
    with e ->
      Timers.exec_timer_pause Timers.M_UF Timers.F_union;
      raise e
  else union env r1 r2 dep


let rec distinct env rl dep =
  Debug.all env;
  let d = LX.mk_distinct false rl in
  Debug.distinct d;
  let env, _, newds =
    List.fold_left
      (fun (env, mapr, newds) r ->
         Options.exec_thread_yield ();
         let rr, ex = Env.find_or_normal_form env r in
         try
           let exr = MapX.find rr mapr in
           Options.tool_req 3 "TR-CCX-Distinct-Conflict";
           raise (Ex.Inconsistent ((Ex.union ex exr), cl_extract env))
         with Not_found ->
           let uex = Ex.union ex dep in
           let mdis =
             try MapX.find rr env.neqs with Not_found -> MapL.empty in
           let mdis =
             try
               MapL.add d (Ex.merge uex (MapL.find d mdis)) mdis
             with Not_found ->
               MapL.add d uex mdis
           in
           let env = Env.init_leaf env rr in
           let env = {env with neqs = MapX.add rr mdis env.neqs} in
           env, MapX.add rr uex mapr, (rr, ex, mapr)::newds
      )
      (env, MapX.empty, [])
      rl
  in
  List.fold_left
    (fun env (r1, ex1, mapr) ->
       MapX.fold (fun r2 ex2 env ->
           let ex = Ex.union ex1 (Ex.union ex2 dep) in
           try match X.solve r1 r2 with
             | [a, b] ->
               if (X.equal a r1 && X.equal b r2) ||
                  (X.equal a r2 && X.equal b r1) then env
               else
                 distinct env [a; b] ex
             | []  ->
               Options.tool_req 3 "TR-CCX-Distinct-Conflict";
               raise (Ex.Inconsistent (ex, cl_extract env))
             | _   -> env
           with Util.Unsolvable -> env) mapr env)
    env newds

let distinct env rl dep =
  let env = distinct env rl dep in
  Debug.check_invariants "distinct" env;
  env

let are_equal env t1 t2 ~added_terms =
  if E.equal t1 t2 then Some (Ex.empty, cl_extract env)
  else
    let lookup =
      if added_terms then Env.lookup_by_t
      else Env.lookup_by_t___without_failure
    in
    let r1, ex_r1 = lookup t1 env in
    let r2, ex_r2 = lookup t2 env in
    if X.equal r1 r2 then Some (Ex.union ex_r1 ex_r2, cl_extract env)
    else None

let are_distinct env t1 t2 =
  Debug.are_distinct t1 t2;
  let r1, ex_r1 = Env.lookup_by_t t1 env in
  let r2, ex_r2 = Env.lookup_by_t t2 env in
  try
    ignore (union env r1 r2 (Ex.union ex_r1 ex_r2));
    None
  with Ex.Inconsistent (ex, classes) -> Some (ex, classes)

let already_distinct env lr =
  let d = LX.mk_distinct false lr in
  try
    List.iter (fun r ->
        let mdis = MapX.find r env.neqs in
        ignore (MapL.find d mdis)
      ) lr;
    true
  with Not_found -> false

let find env t =
  Options.tool_req 3 "TR-UFX-Find";
  Env.lookup_by_t t env

let find_r =
  Options.tool_req 3 "TR-UFX-Find";
  Env.find_or_normal_form

let print = Debug.all

let mem = Env.mem

let class_of env t =
  try
    let rt, _ = MapX.find (ME.find t env.make) env.repr in
    MapX.find rt env.classes
  with Not_found -> SE.singleton t

let rclass_of env r =
  try MapX.find r env.classes
  with Not_found -> SE.empty

let term_repr uf t =
  let st = class_of uf t in
  try SE.min_elt st
  with Not_found -> t

let class_of env t = SE.elements (class_of env t)

let empty () =
  let env = {
    make  = ME.empty;
    repr = MapX.empty;
    classes = MapX.empty;
    gamma = MapX.empty;
    neqs = MapX.empty;
    ac_rs = RS.empty
  }
  in
  let env, _ = add env E.vrai in
  let env, _ = add env E.faux in
  distinct env [X.top (); X.bot ()] Ex.empty

let make uf t = ME.find t uf.make

(*** add wrappers to profile exported functions ***)

let add env t =
  if Options.get_timers() then
    try
      Timers.exec_timer_start Timers.M_UF Timers.F_add_terms;
      let res = add env t  in
      Timers.exec_timer_pause Timers.M_UF Timers.F_add_terms;
      res
    with e ->
      Timers.exec_timer_pause Timers.M_UF Timers.F_add_terms;
      raise e
  else add env t


let is_normalized env r =
  List.for_all
    (fun x ->
       try X.equal x (fst (MapX.find x env.repr))
       with Not_found -> true)
    (X.leaves r)

let distinct_from_constants rep env =
  let neqs = try MapX.find rep env.neqs with Not_found -> assert false in
  MapL.fold
    (fun lit _ acc ->
       let contains_rep = ref false in
       let lit_vals =
         match LX.view lit with
         | Xliteral.Distinct (_, l) -> l
         | _ -> []
       in
       let acc2 =
         List.fold_left
           (fun acc r ->
              if X.equal rep r then contains_rep := true;
              match X.leaves r with
              | [] -> r::acc
              | _ -> acc
           )acc lit_vals
       in
       if !contains_rep then acc2 else acc
    )neqs []

let assign_next env =
  let acc = ref None in
  let res, env =
    try
      MapX.iter
        (fun r eclass ->
           let eclass =
             try SE.fold (fun t z -> (t, ME.find t env.make)::z) eclass []
             with Not_found -> assert false
           in
           let opt =
             X.assign_value r (distinct_from_constants r env) eclass
           in
           match opt with
           | None -> ()
           | Some (s, is_cs) -> acc := Some (s, r, is_cs); raise Exit
        )env.classes;
      [], env (* no cs *)
    with Exit ->
    match !acc with
    | None -> assert false
    | Some (s, rep, is_cs) ->
      if get_debug_interpretation () then
        Printer.print_dbg
          ~module_name:"Uf" ~function_name:"assign_next"
          "TRY assign-next %a = %a" X.print rep E.print s;
        (*
          !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
          modify this to be able to returns CS on terms. This way,
          we will not modify env in this function
          !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
        *)
      let env, _ =  add env s in (* important for termination *)
      let eq = LX.view (LX.mk_eq rep (make env s)) in
      [eq, is_cs, Th_util.CS (None, Th_util.Th_UF, Numbers.Q.one)], env
  in
  Debug.check_invariants "assign_next" env;
  res, env


(**** Counter examples functions ****)
let is_a_good_model_value (x, _) =
  match X.leaves x with
    [] -> true
  | [y] -> X.equal x y
  | _ -> false

let is_const_term (x, _) =
  match X.term_extract x with
  | Some t, _ ->
    E.const_term t
  | _ ->
    (*cannot test for theories which don't implement term_extract*)
    true

let model_repr_of_term t env mrepr unbounded =
  try ME.find t mrepr, mrepr
  with Not_found ->
    let mk = try ME.find t env.make with Not_found -> assert false in
    let rep,_ = try MapX.find mk env.repr with Not_found -> assert false in
    match unbounded with
    | Some string_repr -> (rep, string_repr), mrepr
    | None ->
      let cls =
        try SE.elements (MapX.find rep env.classes)
        with Not_found -> assert false
      in
      let cls =
        try List.rev_map (fun s -> s, ME.find s env.make) cls
        with Not_found -> assert false
      in
      let e = X.choose_adequate_model t rep cls in
      e, ME.add t e mrepr

let is_optimization_op = function
  | Sy.Op Sy.Optimize _ -> true
  | _ -> false

let compute_concrete_model_of_val
    env t ((fprofs, cprofs, carrays, mrepr) as acc) unbounded =
  let { E.f; xs; ty; _ } =
    match E.term_view t with
    | E.Not_a_term _ -> assert false
    | E.Term tt -> tt
  in
  if X.is_solvable_theory_symbol f ty
  || E.is_fresh t || E.is_fresh_skolem t
  || E.equal t E.vrai || E.equal t E.faux
  || is_optimization_op f
  then
    acc
  else
    let xs, tys, mrepr =
      List.fold_left
        (fun (xs, tys, mrepr) x ->
           let rep_x, mrepr = model_repr_of_term x env mrepr None in
           assert (is_const_term rep_x);
           (x, rep_x)::xs,
           (E.type_info x)::tys,
           mrepr
        ) ([],[], mrepr) (List.rev xs)
    in
    let rep, mrepr = model_repr_of_term t env mrepr unbounded in
    assert (is_a_good_model_value rep);
    assert (is_const_term rep);
    match f, xs, ty with
    | Sy.Op Sy.Set, _, _ -> acc

    | Sy.Op Sy.Get, [(_,(a,_));((_,(i,_)) as e)], _ ->
      begin
        match X.term_extract a with
        | Some ta, true ->
          let { E.f = f_ta; xs=xs_ta; _ } =
            match E.term_view ta with
            | E.Not_a_term _ -> assert false
            | E.Term tt -> tt
          in
          assert (xs_ta == []);
          fprofs,
          cprofs,
          Profile.add (f_ta,[X.type_info i], ty) ([e], rep) carrays,
          mrepr

        | _ -> assert false
      end

    | _ ->
      if tys == [] then
        fprofs, Profile.add (f, tys, ty) (xs, rep) cprofs, carrays,
        mrepr
      else
        Profile.add (f, tys, ty) (xs, rep) fprofs, cprofs, carrays,
        mrepr


(* A map of expressions / terms, ordered by depth first, and then by
   Expr.compare for expressions with same depth. This structure will
   be used to build a model, by starting with the inner/smaller terms
   first. The values associated to the key will be their make *)
module MED = Map.Make
    (struct
      type t = Expr.t
      let compare a b =
        let c = Expr.depth a - Expr.depth b in
        if c <> 0 then c
        else Expr.compare a b
    end)

let terms env = ME.fold MED.add env.make MED.empty

let compute_concrete_model ?(inline_obj_in_model=Util.MI.empty) env =
  let bounded, pinfty, minfty =
    Util.MI.fold
      (fun _ord v ((bounded, pinfty, minfty) as acc) ->
         let {Th_util.value; r; order = _; is_max = _; e=_} = v in
         match value with
         | Value _ ->
           SetX.add v.Th_util.r bounded, pinfty, minfty
         | Pinfinity  -> bounded, SetX.add r pinfty, minfty
         | Minfinity -> bounded, pinfty, SetX.add r minfty
         | Unknown -> acc
      ) inline_obj_in_model (SetX.empty, SetX.empty, SetX.empty)
  in
  let not_unbounded = pinfty == SetX.empty && minfty == SetX.empty in
  (* Here, we fold on each term that appears in the 'make' map,
     starting from those with smaller depth, and we compute a concrete
     model for it. For the objectives (if any), we check if it should
     be +/- infinity *)
  MED.fold
    (fun t mk acc ->
       if SetX.mem mk pinfty then
         (* mk's optimum is +infinity *)
         compute_concrete_model_of_val env t acc (Some "+oo")
       else
       if SetX.mem mk minfty then
         (* mk's optimum is -infinity *)
         compute_concrete_model_of_val env t acc (Some "-oo")
       else
       if not_unbounded || SetX.mem mk bounded then
         (* either the pb is bounded (or it isn't an optimization pb)
            or we have an optimum for mk *)
         compute_concrete_model_of_val env t acc None
       else
         acc
    ) (terms env)
    (
      Profile.empty, (* functions profile *)
      Profile.empty, (* constants profile *)
      Profile.empty, (* arrays profile *)
      (ME.empty : (r * string) ME.t) (* a mapping from terms to
                                        representatives/values in
                                        model as a semantic value and
                                        as a string *)
    )

let compute_objectives optimized_splits env mrepr =
  let seen_infinity = ref false in
  Util.MI.map
    (fun {Th_util.e; value; r=_; is_max=_; order=_} ->
       e,
       (if !seen_infinity then begin
           (* every objective after 'oo' is printed as ]-oo, +oo[ *)
           Models.Obj_unk
         end
        else
          match value with
          | Pinfinity -> seen_infinity := true; Obj_pinfty
          | Minfinity -> seen_infinity := true; Obj_minfty
          | Value _ ->
            let (_r_x, r_s), _mrepr = model_repr_of_term e env mrepr None in
            Obj_val r_s
          | Unknown ->
            (* in this case, we should have !seen_infinity == true.
               Which is handled in the if branch. Moreover, we
               continue optimization now even if infinity is
               encountered. *)
            assert false
       )
    )optimized_splits

let extract_concrete_model ~prop_model ~optimized_splits env =
  if get_interpretation () then
    Some (lazy (
        let inline_obj_in_model =
          if Options.get_objectives_in_interpretation() then
            (* take optimized_splits into account for model, but don't
               print it in a separate section *)
            optimized_splits
          else
            Util.MI.empty
        in
        let functions, constants, arrays, mrepr =
          compute_concrete_model env ~inline_obj_in_model
        in
        let objectives = compute_objectives optimized_splits env mrepr in
        { Models.propositional = prop_model;
          functions; constants; arrays; objectives;
          terms_values = mrepr }
      ))
  else
    None
