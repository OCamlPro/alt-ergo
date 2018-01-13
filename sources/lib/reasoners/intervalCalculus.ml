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
(*     Copyright (C) 2013-2017 --- OCamlPro SAS                               *)
(*                                                                            *)
(*     This file is distributed under the terms of the Apache Software        *)
(*     License version 2.0                                                    *)
(*                                                                            *)
(******************************************************************************)

open Format
open Options
open Sig
open Matching_types

module Z = Numbers.Z
module Q = Numbers.Q

let ale = Hstring.make "<="
let alt = Hstring.make "<"
let is_le n = Hstring.compare n ale = 0
let is_lt n = Hstring.compare n alt = 0

let (-@) l1 l2 = List.rev_append l1 l2

module L = Literal
module Sy = Symbols
module I = Intervals

module OracleContainer =
  (val (Inequalities.get_current ()) : Inequalities.Container_SIG)


module Make
  (X : Sig.X)
  (Uf : Uf.S with type r = X.r)
  (P : Polynome.EXTENDED_Polynome with type r = X.r) = struct

    module MP0 = Map.Make(P)
    module SP = Set.Make(P)
    module SX = Set.Make(struct type t = X.r let compare = X.hash_cmp end)
    module MX0 = Map.Make(struct type t = X.r let compare = X.hash_cmp end)
    module MPL = Literal.LT.Map


    module Oracle = OracleContainer.Make(X)(Uf)(P)

    module MF = Formula.Map
    module ST = Term.Set
    module MT = Term.Map
    module F = Formula
    module Ex = Explanation

    module EM = Matching.Make
      (struct
        include Uf
        let add_term env t = fst (Uf.add env t)
        let are_equal env s t ~add_terms =
          Uf.are_equal env s t ~added_terms:false
      end)

    type r = P.r
    type uf = Uf.t
    module LR =
      Literal.Make(struct type t = X.r let compare = X.hash_cmp include X end)

    module MR = Map.Make(
      struct
        type t = r L.view
        let compare a b = LR.compare (LR.make a) (LR.make b)
      end)

    let alien_of p = match P.is_monomial p with
      | Some (a,x,b) when Q.equal a Q.one && Q.sign b = 0 -> x
      | _ -> P.embed p

    let poly_of r =
      match P.extract r with
      | Some p -> p
      | None ->
        P.create
          [Numbers.Q.one, r] Numbers.Q.zero (X.type_info r)

    module SimVar = struct
      type t = X.r
      let compare = X.hash_cmp
      let is_int r = X.type_info r == Ty.Tint
      let print fmt x =
        match P.extract x with
        | None -> fprintf fmt "%a" X.print x
        | Some p -> fprintf fmt "s!%d" (X.hash x) (* slake vars *)
    end

    module Sim = OcplibSimplex.Basic.Make(SimVar)(Numbers.Q)(Explanation)

    type t = {
      inequations : Oracle.t MPL.t;
      monomes: (I.t * SX.t) MX0.t;
      polynomes : I.t MP0.t;
      known_eqs : SX.t;
      improved_p : SP.t;
      improved_x : SX.t;
      classes : Term.Set.t list;
      size_splits : Q.t;
      int_sim : Sim.Core.t;
      rat_sim : Sim.Core.t;
      new_uf : uf;
      th_axioms : Commands.th_elt MF.t;
      linear_dep : ST.t MT.t;
      syntactic_matching :
        (Matching_types.trigger_info * Matching_types.gsubst list) list list;
    }

    module Sim_Wrap = struct

      let check_unsat_result simplex env =
        match Sim.Result.get None simplex with
        | Sim.Core.Unknown -> assert false
        | Sim.Core.Unbounded _ -> assert false
        | Sim.Core.Max _ -> assert false
        | Sim.Core.Sat _ -> ()
        | Sim.Core.Unsat ex ->
          let ex = Lazy.force ex in
          if debug_fm() then
            fprintf fmt "[fm] simplex derived unsat: %a@." Explanation.print ex;
          raise (Exception.Inconsistent (ex, env.classes))

      let solve env i =
        let int_sim = Sim.Solve.solve env.int_sim in
        check_unsat_result int_sim env;
        let rat_sim = Sim.Solve.solve env.rat_sim in
        check_unsat_result rat_sim env;
        {env with int_sim; rat_sim}


      let solve env i =
      if Options.timers() then
        try
	  Timers.exec_timer_start Timers.M_Simplex Timers.F_solve;
	  let res = solve env i in
	  Timers.exec_timer_pause Timers.M_Simplex Timers.F_solve;
	  res
        with e ->
	  Timers.exec_timer_pause Timers.M_Simplex Timers.F_solve;
	  raise e
      else solve env i


      let extract_bound i get_lb =
        let func, q =
          if get_lb then I.borne_inf, Q.one else I.borne_sup, Q.m_one in
        try
          let bnd, expl, large = func i in
          Some (bnd, if large then Q.zero else q), expl
        with I.No_finite_bound -> None, Explanation.empty

      let same_bnds _old _new =
        match _old, _new with
        | None, None -> true
        | None, Some _ | Some _, None -> false
        | Some(s,t), Some(u, v) -> Q.equal s u && Q.equal t v

      let add_if_better p _old _new simplex =
        (* p is in normal form pos *)
        let old_mn, old_mn_ex = extract_bound _old true in
        let old_mx, old_mx_ex = extract_bound _old false in
        let new_mn, new_mn_ex = extract_bound _new true in
        let new_mx, new_mx_ex = extract_bound _new false in
        if same_bnds old_mn new_mn && same_bnds old_mx new_mx then simplex
        else
          let l, z = P.to_list p in
          assert (Q.sign z = 0);
          let simplex, changed =
            match l with
              [] -> assert false
            | [c, x] ->
              assert (Q.is_one c);
              Sim.Assert.var simplex x new_mn new_mn_ex new_mx new_mx_ex
            | _ ->
              let l = List.rev_map (fun (c, x) -> x, c) l in
              Sim.Assert.poly simplex (Sim.Core.P.from_list l) (alien_of p)
                new_mn new_mn_ex new_mx new_mx_ex
          in
          (* we don't solve immediately. It may be expensive *)
          simplex


      let finite_non_point_dom info =
        match info.Sim.Core.mini, info.Sim.Core.maxi with
        | None, _ | _, None -> None
        | Some (a, b), Some(x,y) ->
          assert (Q.is_zero b); (*called on integers only *)
          assert (Q.is_zero y);
          let c = Q.compare a x in
          assert (c <= 0); (* because simplex says sat *)
          if c = 0 then None else Some (Q.sub x a)

      (* not used for the moment *)
      let case_split =
        let gen_cs x n s orig =
          if debug_fm () then
            fprintf fmt "[Sim_CS-%d] %a = %a of size %a@."
              orig X.print x Q.print n  Q.print s;
          let ty = X.type_info x in
          let r1 = x in
	  let r2 = alien_of (P.create [] n  ty) in
	  [LR.mkv_eq r1 r2, true, CS (Th_arith, s)]
        in
        let aux_1 uf x (info,_) acc =
          assert (X.type_info x == Ty.Tint);
          match finite_non_point_dom info with
          | Some s when
              (Sim.Core.equals_optimum info.Sim.Core.value info.Sim.Core.mini ||
                 Sim.Core.equals_optimum info.Sim.Core.value info.Sim.Core.maxi)
              && Uf.is_normalized uf x ->
            let v, _ = info.Sim.Core.value in
            assert (Q.is_int v);
            begin
              match acc with
              | Some (_,_,s') when Q.compare s' s <= 0 -> acc
              | _ -> Some (x,v, s)
            end
          | _ -> acc
        in
        let aux_2 env uf x (info,_) acc =
          let v, _ = info.Sim.Core.value in
          assert (X.type_info x == Ty.Tint);
          match finite_non_point_dom info with
          | Some s when Q.is_int v && Uf.is_normalized uf x ->
            let fnd1, cont1 =
              try true, I.contains (fst (MX0.find x env.monomes)) v
              with Not_found -> false, true
            in
            let fnd2, cont2 =
              try true, I.contains (MP0.find (poly_of x) env.polynomes) v
              with Not_found -> false, true
            in
            if (fnd1 || fnd2) && cont1 && cont2 then
              match acc with
              | Some (_,_,s') when Q.compare s' s <= 0 -> acc
              | _ -> Some (x,v, s)
            else
              acc
          | _ -> acc
        in
        fun env uf ->
          let int_sim = env.int_sim in
          assert (int_sim.Sim.Core.status == Sim.Core.SAT);
          let acc =
            Sim.Core.MX.fold (aux_1 uf) int_sim.Sim.Core.non_basic None
          in
          let acc =
            Sim.Core.MX.fold (aux_1 uf) int_sim.Sim.Core.basic acc
          in
          match acc with
          | Some (x, n, s) -> gen_cs x n s 1
            (*!!!disable case-split that separates and interval into two parts*)
          | None ->
            let acc =
              Sim.Core.MX.fold (aux_2 env uf) int_sim.Sim.Core.non_basic None
            in
            let acc =
              Sim.Core.MX.fold (aux_2 env uf) int_sim.Sim.Core.basic acc
            in
            match acc with
            | Some (x, n, s) -> gen_cs x n s 2
            | None -> []


      let infer_best_bounds env p =
        let best_bnd lp ~upper sim i set_new_bound =
          let q = if upper then Q.one else Q.m_one in
          let lp = List.rev_map (fun (c, x) -> x, Q.mult q c) lp in
          let sim, mx_res = Sim.Solve.maximize sim (Sim.Core.P.from_list lp) in
          match Sim.Result.get mx_res sim with
          | Sim.Core.Unknown -> assert false
          | Sim.Core.Sat _   -> assert false (* because we maximized *)
          | Sim.Core.Unsat _ -> assert false (* we know sim is SAT *)
          | Sim.Core.Unbounded _ -> i
          | Sim.Core.Max(mx,sol) ->
            let {Sim.Core.max_v; is_le; reason} = Lazy.force mx in
            set_new_bound reason (Q.mult q max_v) ~is_le:is_le i
        in
        if debug_fpa()>=2 then fprintf fmt "#infer bounds for %a@." P.print p;
        let ty = P.type_info p in
        let sim = if ty == Ty.Tint then env.int_sim else env.rat_sim in
        let i = I.undefined ty in
        let lp, c = P.to_list p in
        assert (Q.is_zero c);
        assert (sim.Sim.Core.status == Sim.Core.SAT);
        let i = best_bnd lp ~upper:true sim i I.new_borne_sup in
        let i = best_bnd lp ~upper:false sim i I.new_borne_inf in
        if debug_fpa () >= 2 then
          fprintf fmt "## inferred bounds for %a: %a@." P.print p I.print i;
        i

    end

    module MP = struct
      include MP0

      let assert_normalized_poly p =
        assert
          (let p0, c0, d0 = P.normal_form_pos p in
           let b = Q.is_zero c0 && Q.is_one d0 in
           begin
             if not b then
               fprintf fmt "[IC.assert_normalized_poly] %a is not normalized@."
                 P.print p
           end;
           b)

      let n_add p i old ({polynomes} as env) =
        (*NB: adding a new entry into the map is considered as an improvement*)
        assert_normalized_poly p;
        if I.is_strict_smaller i old || not (MP0.mem p polynomes) then
          let ty = P.type_info p in
          let polynomes = MP0.add p i polynomes in
          let improved_p = SP.add p env.improved_p in
          if ty == Ty.Tint then
            {env with
              polynomes; improved_p;
              int_sim = Sim_Wrap.add_if_better p old i env.int_sim}
          else
            {env with
              polynomes; improved_p;
              rat_sim = Sim_Wrap.add_if_better p old i env.rat_sim}
        else
          let () = assert (I.equal i old) in
          env

      (* find with normalized polys *)
      let n_find p mp =
        assert_normalized_poly p;
        MP0.find p mp

      (* shadow the functions find and add of MP with the ones below
         to force the use of n_find and n_add for normalized polys *)
      let find (_ : unit) (_ : unit) = assert false
      let add (_ : unit) (_ : unit) (_ : unit) = assert false

    end

    module MX = struct
      include MX0

      let assert_is_alien x =
        assert (
          let b = P.extract x == None in
          begin
            if not b then
              fprintf fmt "[IC.assert_is_alien] %a is not an alien@." X.print x
          end;
          b
        )

      let n_add x ((i,_) as e) old ({monomes} as env) =
        (*NB: adding a new entry into the map is considered as an improvement*)
        assert_is_alien x;
        if I.is_strict_smaller i old || not (MX0.mem x monomes) then
          let ty = X.type_info x in
          let monomes = MX0.add x e monomes in
          let improved_x = SX.add x env.improved_x in
          if ty == Ty.Tint then
            {env with
              monomes; improved_x;
              int_sim = Sim_Wrap.add_if_better (poly_of x) old i env.int_sim}
          else
            {env with
              monomes; improved_x;
              rat_sim = Sim_Wrap.add_if_better (poly_of x) old i env.rat_sim}
        else
          let () = assert (I.equal i old) in
          (* because use_x may be updated*)
          {env with monomes = MX0.add x e monomes}


      (* find with real aliens *)
      let n_find x mp =
        assert_is_alien x;
        MX0.find x mp


      (* shadow the functions find and add of MX with the ones below
         to force the use of n_find and n_add for true aliens *)
      let find (_ : unit) (_ : unit) = assert false
      let add (_ : unit) (_ : unit) (_ : unit) = assert false

    end

    (* generic find for values that may be non-alien or non
       normalized polys *)
    let generic_find xp env =
      let is_mon = P.extract xp == None in
      try
        if not is_mon then raise Not_found;
        let i, use = MX.n_find xp env.monomes in i, use, is_mon
      with Not_found ->
        (* according to this implem, it means that we can find aliens in polys
           but not in monomes. FIX THIS => an interval of x in monomes and in
           polys may be differents !!! *)
        let p0 = poly_of xp in
        let p, c = P.separate_constant p0 in
        let p, c0, d = P.normal_form_pos p in
        assert (Q.sign d <> 0 && Q.sign c0 = 0);
        let ty = P.type_info p0 in
        let ip =
          try MP.n_find p env.polynomes with Not_found -> I.undefined ty
        in
        let ip = if Q.is_one d then ip else I.scale d ip in
        let ip =
          if Q.is_zero c then ip
          else I.add ip (I.point c ty Explanation.empty)
        in
        ip, SX.empty, is_mon


    (* generic add for values that may be non-alien or non
       normalized polys *)
    let generic_add x j use is_mon env =
      (* NB: adding an entry into the map is considered as an improvement *)
      let ty = X.type_info x in
      if is_mon then
        try MX.n_add x (j,use) (fst (MX.n_find x env.monomes)) env
        with Not_found -> MX.n_add x (j, use) (I.undefined ty) env
      else
        let p0 = poly_of x in
        let p, c = P.separate_constant p0 in
        let p, c0, d = P.normal_form_pos p in
        assert (Q.sign d <> 0 && Q.sign c0 = 0);
        let j = I.add j (I.point (Q.minus c) ty Explanation.empty) in
        let j = I.scale (Q.inv d) j in
        try MP.n_add p j (MP.n_find p env.polynomes) env
        with Not_found -> MP.n_add p j (I.undefined ty) env


    (*BISECT-IGNORE-BEGIN*)
    module Debug = struct

      let assume a expl =
        if debug_fm () then begin
	  fprintf fmt "[fm] We assume: %a@." LR.print (LR.make a);
	  fprintf fmt "explanations: %a@." Explanation.print expl
        end

      let print_use fmt use =
        SX.iter (fprintf fmt "%a, " X.print) use

      let env env =
        if debug_fm () then begin
	  fprintf fmt "------------ FM: inequations-------------------------@.";
          MPL.iter
            (fun a {Oracle.ple0=p; is_le=is_le} ->
              fprintf fmt "%a%s0  |  %a@."
                P.print p (if is_le then "<=" else "<") L.LT.print a
            )env.inequations;
          fprintf fmt "------------ FM: monomes ----------------------------@.";
	  MX.iter
	    (fun x (i, use) ->
	      fprintf fmt "%a : %a |-use-> {%a}@."
		X.print x I.print i print_use use)
	    env.monomes;
	  fprintf fmt "------------ FM: polynomes---------------------------@.";
	  MP.iter
	    (fun p i ->
	      fprintf fmt "%a : %a@."
		P.print p I.print i)
	    env.polynomes;
	  fprintf fmt "-----------------------------------------------------@."
        end

      let implied_equalities l =
        if debug_fm () then
          begin
            fprintf fmt "[fm] %d implied equalities@." (List.length l);
            List.iter
	      (fun (ra, _, ex, _) ->
                fprintf fmt "  %a %a@."
		  LR.print (LR.make ra) Explanation.print ex) l
          end

      let case_split r1 r2 =
	if debug_fm () then
	  fprintf fmt "[case-split] %a = %a@." X.print r1 X.print r2

      let no_case_split s =
	if debug_fm () then fprintf fmt "[case-split] %s : nothing@." s


      let inconsistent_interval expl =
	if debug_fm () then
	  fprintf fmt "interval inconsistent %a@." Explanation.print expl

      let added_inequation kind ineq =
        if debug_fm () then begin
          fprintf fmt "[fm] I derived the (%s) inequality: %a %s 0@."
            kind P.print ineq.Oracle.ple0
            (if ineq.Oracle.is_le then "<=" else "<");
          fprintf fmt "from the following combination:@.";
          Util.MI.iter
            (fun a (coef, ple0, is_le) ->
              fprintf fmt "\t%a * (%a %s 0) + @."
                Q.print coef P.print ple0 (if is_le then "<=" else "<")
            )ineq.Oracle.dep;
          fprintf fmt "\t0@.@."
        end

      let tighten_interval_modulo_eq p1 p2 i1 i2 b1 b2 j =
        if debug_fm () then begin
          fprintf fmt "@.[fm] tighten intervals modulo eq: %a = %a@."
            P.print p1 P.print p2;
          fprintf fmt "  %a has interval %a@." P.print p1 I.print i1;
          fprintf fmt "  %a has interval %a@." P.print p2 I.print i2;
          fprintf fmt "  intersection is %a@." I.print j;
          if b1 then fprintf fmt "  > improve interval of %a@.@." P.print p1;
          if b2 then fprintf fmt "  > improve interval of %a@.@." P.print p2;
          if not b1 && not b2 then fprintf fmt "  > no improvement@.@."
        end

    end
    (*BISECT-IGNORE-END*)

    let empty classes = {
      inequations = MPL.empty;
      monomes = MX.empty ;
      polynomes = MP.empty ;
      known_eqs = SX.empty ;
      improved_p = SP.empty ;
      improved_x = SX.empty ;
      classes = classes;
      size_splits = Q.one;
      new_uf = Uf.empty ();

      rat_sim =
        Sim.Solve.solve
          (Sim.Core.empty ~is_int:false ~check_invs:false ~debug:0);
      int_sim =
        Sim.Solve.solve
          (Sim.Core.empty ~is_int:true ~check_invs:false ~debug:0);

      th_axioms = MF.empty;
      linear_dep = MT.empty;
      syntactic_matching = [];
    }

    (*let up_improved env p oldi newi =
      if I.is_strict_smaller newi oldi then
      { env with improved = SP.add p env.improved }
      else env*)


    (** computes an interval for vars = x_1^n_1 * ..... * x_i^n_i
        (1) if some var is not in monomes, then return undefined
        (2) check that all vars are in monomes before doing interval ops **)
    let mult_bornes_vars vars env ty =
      try
        let l =
          List.rev_map (fun (y,n) ->
            let i, _, _ = generic_find y env in i, n
          ) vars
        in
        List.fold_left
          (fun ui (yi,n) -> I.mult ui (I.power n yi))
          (I.point Q.one ty Explanation.empty) l
      with Not_found -> I.undefined ty

    (** computes the interval of a polynome from those of its monomes.
        The monomes are supposed to be already added in env **)
    let intervals_from_monomes ?(monomes_inited=true) env p =
      let pl, v = P.to_list p in
      List.fold_left
        (fun i (a, x) ->
	  let i_x, _  =
            try MX.n_find x env.monomes
            with Not_found ->
              if monomes_inited then assert false;
              I.undefined (X.type_info x), SX.empty
          in
	  I.add (I.scale a i_x) i
        ) (I.point v (P.type_info p) Explanation.empty) pl


    (* because, it's not sufficient to look in the interval that corresponds to
       the normalized form of p ... *)
    let cannot_be_equal_to_zero env p ip =
      try
        let z = alien_of (P.create [] Q.zero (P.type_info p)) in
        match X.solve (alien_of p) z with
	| [] -> Sig.No (* p is equal to zero *)
	| _ -> I.doesnt_contain_0 ip
      with Exception.Unsolvable -> Sig.Yes (Explanation.empty, env.classes)


    let rec init_monomes_of_poly are_eq env p use_p expl =
      List.fold_left
        (fun env (_, x) ->
          try
            let u, old_use_x = MX.n_find x env.monomes in
            MX.n_add x (u, SX.union old_use_x use_p) u env
          with Not_found ->
            update_monome are_eq expl use_p env x
        ) env (fst (P.to_list p))

    and init_alien are_eq expl p (normal_p, c, d) ty use_x env =
      let env = init_monomes_of_poly are_eq env p use_x expl in
      let i = intervals_from_monomes env p in
      let i =
        try
	  let old_i = MP.n_find normal_p env.polynomes in
	  let old_i = I.scale d
	    (I.add old_i (I.point c ty Explanation.empty)) in
	  I.intersect i old_i
        with Not_found -> i
      in
      env, i



    and update_monome are_eq expl use_x env x =
      let ty = X.type_info x in
      let ui, env = match  X.ac_extract x with
        | Some {h=h; l=l }
	    when Symbols.equal h (Symbols.Op Symbols.Mult) ->
	  let use_x = SX.singleton x in
	  let env =
	    List.fold_left
	      (fun env (r,_) ->
                let rp, _, _ = poly_of r |> P.normal_form_pos in
                match P.is_monomial rp with
                | Some (a,y,b) when Q.equal a Q.one && Q.sign b = 0 ->
	          update_monome are_eq expl use_x env y
                | _ -> env (* should update polys ? *)
              ) env l in
	  let m = mult_bornes_vars l env ty in
	  m, env
        | _ ->
	  match X.term_extract x with
	  | Some t, _ ->
	    let use_x = SX.singleton x in
	    begin
	      match Term.view t with
	      | {Term.f = (Sy.Op Sy.Div); xs = [a; b]} ->
                let ra, ea =
                  let (ra, _) as e = Uf.find env.new_uf a in
                  if List.filter (X.equal x) (X.leaves ra) == [] then e
                  else fst (X.make a), Explanation.empty (*otherwise, we loop*)
                in
                let rb, eb =
                  let (rb, _) as e = Uf.find env.new_uf b in
                  if List.filter (X.equal x) (X.leaves rb) == [] then e
                  else fst (X.make b), Explanation.empty (*otherwise, we loop*)
                in
                let expl = Explanation.union expl (Explanation.union ea eb) in
		let pa = poly_of ra in
		let pb = poly_of rb in
		let (pa', ca, da) as npa = P.normal_form_pos pa in
		let (pb', cb, db) as npb = P.normal_form_pos pb in
		let env, ia =
		  init_alien are_eq expl pa npa ty use_x env in
                let ia = I.add_explanation ia ea in (* take repr into account*)
		let env, ib =
		  init_alien are_eq expl pb npb ty use_x env in
                let ib = I.add_explanation ib eb in (* take repr into account*)
		let ia, ib = match cannot_be_equal_to_zero env pb ib with
		  | Yes (ex, _) when Q.equal ca cb
		      && P.compare pa' pb' = 0 ->
		    let expl = Explanation.union ex expl in
		    I.point da ty expl, I.point db ty expl
		  | Yes (ex, _) ->
		    begin
		      match are_eq a b with
		      | Yes (ex_eq, _) ->
			let expl = Explanation.union ex expl in
			let expl = Explanation.union ex_eq expl in
			I.point Q.one ty expl,
			I.point Q.one ty expl
		      | No -> ia, ib
		    end
		  | No -> ia, ib
		in
		I.div ia ib, env
	      | _ -> I.undefined ty, env
	    end
	  | _ -> I.undefined ty, env
      in
      let u, use_x' =
        try MX.n_find x env.monomes
        with Not_found -> I.undefined (X.type_info x), use_x in
      let ui = I.intersect ui u in
      MX.n_add x (ui, (SX.union use_x use_x')) u env

    let rec tighten_ac are_eq x env expl =
      let ty = X.type_info x in
      let u, use_x =
        try MX.n_find x env.monomes
        with Not_found -> I.undefined ty, SX.empty in
      try
        match X.ac_extract x with
	| Some {h=h;t=t;l=[x,n]}
            when Symbols.equal h (Symbols.Op Symbols.Mult) && n mod 2 = 0  ->
          let env = match P.extract x with
            | None ->
              begin
              (* identity *)
	        let u = I.root n u in
	        let (pu, use_px) =
	          try MX.n_find x env.monomes (* we know that x is a monome *)
	          with Not_found -> I.undefined ty, SX.empty
	        in
	        let u = I.intersect u pu in
                let env = MX.n_add x (u, use_px) pu env in
	        tighten_non_lin are_eq x use_px env expl
              end
            | Some _ ->
              (* Do something else for polys and non normalized-monomes ? *)
              env
          in
          env
	| Some {h=h;t=t;l=[x,n]} when
            Symbols.equal h (Symbols.Op Symbols.Mult) && n > 2 ->
          let env = match P.extract x with
            | None ->
              begin
	        let u = I.root n u in
	        let pu, use_px =
	          try MX.n_find x env.monomes (* we know that x is a monome *)
	          with Not_found -> I.undefined ty, SX.empty
	        in
	        let u = I.intersect u pu in
                let env = MX.n_add x (u, use_px) pu env in
	        tighten_non_lin are_eq x use_px env expl
              end
            | Some _ ->
              (* Do something else for polys and non normalized-monomes ? *)
              env
          in
          env
	| _ -> env
      with Q.Not_a_float -> env


    and tighten_div x env expl =
      env

    and tighten_non_lin are_eq x use_x env expl =
      let env' = tighten_ac are_eq x env expl in
      let env' = tighten_div x env' expl in
      (*let use_x = SX.union use1_x use2_x in*)
      (* let i, _ = MX.find x env.monomes in *)
      (*let env' = update_monome are_eq expl use_x env' x in too expensive*)
      SX.fold
        (fun x acc ->
	  let _, use = MX.n_find x acc.monomes in (* this is non-lin mult *)
	  (*if I.is_strict_smaller new_i i then*)
	  update_monome are_eq expl use acc x
       (*else acc*))
        use_x env'

    let update_monomes_from_poly p i env =
      let lp, _ = P.to_list p in
      let ty = P.type_info p in
      List.fold_left (fun env (a,x) ->
        let np = P.remove x p in
        let (np,c,d) = P.normal_form_pos np in
        try
	  let inp = MP.n_find np env.polynomes in
	  let new_ix =
	    I.scale
	      (Q.div Q.one a)
	      (I.add i
	         (I.scale (Q.minus d)
		    (I.add inp
		       (I.point c ty Explanation.empty)))) in
	  let old_ix, ux = MX.n_find x env.monomes in
	  let ix = I.intersect old_ix new_ix in
          MX.n_add x (ix, ux) old_ix env
        with Not_found -> env
      ) env lp

    let update_polynomes_intervals env =
      MP.fold
        (fun p ip env ->
	  let new_i = intervals_from_monomes env p in
	  let i = I.intersect new_i ip in
	  if I.is_strict_smaller i ip then
            update_monomes_from_poly p i (MP.n_add p i ip env)
	  else env
        ) env.polynomes env

    let update_non_lin_monomes_intervals are_eq env =
      MX.fold
        (fun x (_, use_x) env ->
          tighten_non_lin are_eq x use_x env Explanation.empty
        ) env.monomes env

    let find_one_eq x u =
      match I.is_point u with
      | Some (v, ex) when X.type_info x != Ty.Tint || Q.is_int v ->
        let eq =
	  LR.mkv_eq x (alien_of (P.create [] v (X.type_info x))) in
	Some (eq, None, ex, Sig.Other)
      | _ -> None

    let find_eq eqs x u env =
      match find_one_eq x u with
      | None -> eqs
      | Some eq1 ->
	begin
          match X.ac_extract x with
	  | Some {h = h; l = [y,n]}
	      when Symbols.equal h (Symbols.Op Symbols.Mult) ->
	    let neweqs = try
		           let u, _, _ = generic_find y env in
		           match find_one_eq y u with
		           | None -> eq1::eqs
		           | Some eq2 -> eq1::eq2::eqs
	      with Not_found -> eq1::eqs
	    in neweqs
	  | _ -> eq1::eqs
	end

    type ineq_status =
    | Trivial_eq
    | Trivial_ineq of Q.t
    | Bottom
    | Monome of Q.t * P.r * Q.t
    | Other

    let ineq_status {Oracle.ple0 = p ; is_le = is_le} =
      match P.is_monomial p with
	Some (a, x, v) -> Monome (a, x, v)
      | None ->
	if P.is_empty p then
	  let _, v = P.separate_constant p in
	  let c = Q.sign v (* equiv. to compare v Q.zero *) in
	  if c > 0 || (c >=0 && not is_le) then Bottom
	  else
	    if c = 0 && is_le then Trivial_eq
	    else Trivial_ineq v
	else Other

    (*let ineqs_from_dep dep borne_inf is_le =
      List.map
      (fun {poly_orig = p; coef = c} ->
      let (m,v,ty) = P.mult_const minusone p in
      (* quelle valeur pour le ?????? *)
      { ple0 = {poly = (m, v +/ (Q.div borne_inf c), ty); le = is_le} ;
      dep = []}
      )dep*)

    let mk_equality p =
      let r1 = alien_of p in
      let r2 = alien_of (P.create [] Q.zero (P.type_info p)) in
      LR.mkv_eq r1 r2

    let fm_equalities eqs { Oracle.ple0 = p; dep = dep; expl = ex } =
      Util.MI.fold
	(fun _ (_, p, _) eqs ->
         (mk_equality p, None, ex, Sig.Other) :: eqs
	) dep eqs


    let update_intervals are_eq env eqs expl (a, x, v) is_le =
      let (u0, use_x0) as ixx = MX.n_find x env.monomes in
      let uints, use_x =
        match X.ac_extract x with
	| Some {h=h; l=l} when Symbols.equal h (Symbols.Op Symbols.Mult) ->
	  let m = mult_bornes_vars l env (X.type_info x) in
	  I.intersect m u0, use_x0
	| _ -> ixx
      in
      let b = Q.div (Q.mult Q.m_one v) a in
      let u =
        if Q.sign a > 0 then
	  I.new_borne_sup expl b is_le uints
        else
	  I.new_borne_inf expl b is_le uints in
      let env = MX.n_add x (u, use_x) u0 env in
      let env =  tighten_non_lin are_eq x use_x env expl in
      env, (find_eq eqs x u env)

    let update_ple0 are_eq env p0 is_le expl =
      if P.is_empty p0 then env
      else
        let ty = P.type_info p0 in
        let a, _ = P.choose p0 in
        let p, change =
	  if Q.sign a < 0 then
	    P.mult_const Q.m_one p0, true
	  else p0, false in
        let p, c, _ = P.normal_form p in
        let c = Q.minus c in
        let u =
	  if change then
            I.new_borne_inf expl c is_le (I.undefined ty)
	  else
	    I.new_borne_sup expl c is_le (I.undefined ty) in
        let u, pu =
	  try
            (* p is in normal_form_pos because of the ite above *)
	    let pu = MP.n_find p env.polynomes in
	    let i = I.intersect u pu in
	    i, pu
	  with Not_found -> u, I.undefined ty
        in
        let env =
	  if I.is_strict_smaller u pu then
	    update_monomes_from_poly p u (MP.n_add p u pu env)
	  else env
        in
        match P.to_list p0 with
        | [a,x], v ->
	  fst(update_intervals are_eq env [] expl (a, x, v) is_le)
        | _ -> env

    let register_relationship c x pi expl (x_rels, p_rels) =
      let x_rels =
        let a = Q.minus c, expl in
        let s = Q.sign c in
        assert (s <> 0);
        let low, up =
          try MX0.find x x_rels with Not_found -> MP0.empty, MP0.empty in
        let v =
          if s < 0 then
            MP0.add pi a low, up  (* low_bnd(pi) / (-c) is a low_bnd of x *)
          else
            low, MP0.add pi a up  (* low_bnd(pi) / (-c) is an up_bnd of x *)
        in
        MX0.add x v x_rels
      in
      let p_rels =
        let p0, c0, d0 = P.normal_form_pos pi in
        let b = c, Q.minus c0, Q.minus d0, expl in
        let s = Q.sign d0 in
        assert (s <> 0);
        let low,up =
          try MP0.find p0 p_rels with Not_found -> MX0.empty, MX0.empty in
        let w =
          if s < 0 then
            (*low_bnd(c*x)/(-d0) + (-c0) is a low_bnd of p0*)
            MX0.add x b low, up
          else
            (*low_bnd(c*x)/(-d0) + (-c0) is an up_bnd of p0*)
            low, MX0.add x b up
        in
        MP0.add p0 w p_rels
      in
      x_rels, p_rels


    let add_inequations are_eq acc x_opt lin =
      List.fold_left
        (fun ((env, eqs, rels) as acc) ineq ->
	  let expl = ineq.Oracle.expl in
	  match ineq_status ineq with
	  | Bottom           ->
            Debug.added_inequation "Bottom" ineq;
	    raise (Exception.Inconsistent (expl, env.classes))

	  | Trivial_eq       ->
            Debug.added_inequation "Trivial_eq" ineq;
	    env, fm_equalities eqs ineq, rels

	  | Trivial_ineq  c  ->
            Debug.added_inequation "Trivial_ineq"  ineq;
	    let n, pp =
	      Util.MI.fold
		(fun _ (_, p, is_le) ((n, pp) as acc) ->
		  if is_le then acc else
		    match pp with
		    | Some _ -> n+1, None
		    | None when n=0 -> 1, Some p
		    | _ -> n+1, None) ineq.Oracle.dep (0,None)
	    in
	    let env =
	      Util.MI.fold
		(fun _ (coef, p, is_le) env ->
		  let ty = P.type_info p in
		  let is_le =
		    match pp with
		      Some x -> P.compare x p = 0 | _ -> is_le && n=0
		  in
		  let p' = P.sub (P.create [] (Q.div c coef) ty) p in
		  update_ple0 are_eq env p' is_le expl
		) ineq.Oracle.dep env
	    in
	    env, eqs, rels

	  | Monome (a, x, v) ->
            Debug.added_inequation "Monome" ineq;
	    let env, eqs =
	      update_intervals
                are_eq env eqs expl (a, x, v) ineq.Oracle.is_le
	    in
	    env, eqs, rels

	  | Other            ->
            match x_opt with
            | None -> acc
            | Some x ->
              let ple0 = ineq.Oracle.ple0 in
              let c = try P.find x ple0 with Not_found -> assert false in
              let ple0 = P.remove x ple0 in
              env, eqs, register_relationship c x ple0 ineq.Oracle.expl rels
        ) acc lin

    let split_problem env ineqs aliens =
      let current_age = Oracle.current_age () in
      let l, all_lvs =
        List.fold_left
          (fun (acc, all_lvs) ({Oracle.ple0=p} as ineq) ->


	    match ineq_status ineq with
	    | Trivial_eq | Trivial_ineq _ -> (acc, all_lvs)
	    | Bottom ->
              raise (Exception.Inconsistent (ineq.Oracle.expl, env.classes))
	    | _ ->
              let lvs =
                List.fold_left (fun acc e -> SX.add e acc) SX.empty (aliens p)
              in
              ([ineq], lvs) :: acc , SX.union lvs all_lvs
          )([], SX.empty) ineqs
      in
      let ll =
        SX.fold
          (fun x l ->
            let lx, l_nx = List.partition (fun (_,s) -> SX.mem x s) l in
            match lx with
            | [] -> assert false
            | e:: lx ->
              let elx =
                List.fold_left
                  (fun (l, lvs) (l', lvs') ->
                    List.rev_append l l', SX.union lvs lvs') e lx in
              elx :: l_nx
          ) all_lvs l
      in
      let ll =
        List.filter
          (fun (ineqs, _) ->
            List.exists
              (fun ineq -> Z.equal current_age ineq.Oracle.age) ineqs
          )ll
      in
      List.fast_sort (fun (a,_) (b,_) -> List.length a - List.length b) ll

    let is_normalized_poly uf p =
      let p = alien_of p in
      let rp, _  = Uf.find_r uf p in
      if X.equal p rp then true
      else begin
        fprintf fmt "%a <= 0 NOT normalized@." X.print p;
        fprintf fmt "It is equal to %a@." X.print rp;
        false
      end

    let better_upper_bound_from_intervals env p =
      let p0, c0, d0 = P.normal_form_pos p in
      assert (Q.is_zero c0);
      try
        let i = MP.n_find p0 env.polynomes in
        if Q.is_one d0 then I.borne_sup i
        else
          if Q.is_m_one d0 then
            let bi, ex, is_large = I.borne_inf i in
            Q.minus bi, ex, is_large
          else assert false
      with I.No_finite_bound | Not_found ->
        assert false (*env.polynomes is up to date w.r.t. ineqs *)

    let better_bound_from_intervals env ({Oracle.ple0; is_le; dep} as v) =
      let p, c = P.separate_constant ple0 in
      assert (not (P.is_empty p));
      let cur_up_bnd = Q.minus c in
      let i_up_bnd, expl, is_large = better_upper_bound_from_intervals env p in
      let new_p = P.add_const (Q.minus i_up_bnd) p in
      let a = match Util.MI.bindings dep with [a,_] -> a | _ -> assert false in
      let cmp = Q.compare i_up_bnd cur_up_bnd in
      assert (cmp <= 0);
      if cmp = 0 then
        match is_le, is_large with
        | false, true -> assert false (* intervals are normalized wrt ineqs *)
        | false, false | true, true -> v (* no change *)
        | true , false -> (* better bound, Large ineq becomes Strict *)
          {v with
            Oracle.ple0 = new_p;
            expl = expl;
            is_le = false;
            dep = Util.MI.singleton a (Q.one, new_p, false)}
      else (* new bound is better. i.e. i_up_bnd < cur_up_bnd *)
        {v with
          Oracle.ple0 = new_p;
          expl = expl;
          is_le = is_large;
          dep = Util.MI.singleton a (Q.one, new_p, is_large)}

    let args_of p = List.rev_map snd (fst (P.to_list p))

    let update_linear_dep env rclass_of ineqs =
      let terms =
        List.fold_left
          (fun st {Oracle.ple0} ->
            List.fold_left
              (fun st (c, x) -> ST.union st (rclass_of x))
              st (fst (P.to_list ple0))
          )ST.empty ineqs
      in
      let linear_dep =
        ST.fold
          (fun t linear_dep -> MT.add t terms linear_dep) terms env.linear_dep
      in
      {env with linear_dep}

    let refine_x_bounds ix env rels is_low =
      MP.fold
        (fun p (m_cx, ineq_ex) ix ->
          try
            (* recall (construction of x_rels):
               -> is_low     : low_bnd(pi) / (-c) is a low_bnd of x
               -> not is_low : low_bnd(pi) / (-c) is an up_bnd of x
            *)
            assert (is_low == (Q.sign m_cx > 0));
            let ip, _, _ = generic_find (alien_of p) env in
            let b, ex_b, is_le = I.borne_inf ip in (* invariant, see above *)
            let b = Q.div b m_cx in
            let func = if is_low then I.new_borne_inf else I.new_borne_sup in
            func (Explanation.union ineq_ex ex_b) b is_le ix
          with I.No_finite_bound -> ix
        )rels ix

    let monomes_relational_deductions env x_rels =
      MX.fold
        (fun x (low, up) env ->
          let ix0, use_x =
            try MX.n_find x env.monomes with Not_found -> assert false in
          let ix = refine_x_bounds ix0 env low true in
          let ix = refine_x_bounds ix  env up  false in
          if I.is_strict_smaller ix ix0 then MX.n_add x (ix, use_x) ix0 env
          else env
        )x_rels env

    let refine_p_bounds ip p env rels is_low =
      MX.fold
        (fun x (cx, mc0, md0, ineq_ex) ip ->
          try
            (* recall (construction of p_rels):
               -> is_low     : low_bnd(c*x) / (-d0) + (-c0) is a low_bnd of p0
               -> not is_low : low_bnd(c*x) / (-d0) + (-c0) is an up_bnd of p0
               where p = (p0 + c0) * d0 and c*x + p <= 0
            *)
            assert (is_low == (Q.sign md0 > 0));
            let ix,_ =
              try MX.n_find x env.monomes with Not_found -> raise Exit in
            let bx, ex_b, is_le =
              (if Q.sign cx > 0 then I.borne_inf else I.borne_sup) ix in
            (* this this the low_bnd of c*x, see above *)
            let b = Q.mult cx bx in
            let b = Q.add (Q.div b md0) mc0 in (* final bnd of p0 *)
            let func = if is_low then I.new_borne_inf else I.new_borne_sup in
            func (Explanation.union ineq_ex ex_b) b is_le ip
          with Exit | I.No_finite_bound -> ip
        )rels ip

    let polynomes_relational_deductions env p_rels =
      MP.fold
        (fun p0 (low, up) env ->
          (* p0 is in normal_form pos *)
          let xp = alien_of p0 in
          if not (MP.mem p0 env.polynomes || MX.mem xp env.monomes) then env
          else
            let ip0, use, is_mon = generic_find xp env in
            let ip = refine_p_bounds ip0 p0 env low true in
            let ip = refine_p_bounds ip  p0 env up  false in
            if I.is_strict_smaller ip ip0 then
              if is_mon then MX.n_add xp (ip, use) ip0 env
              else MP.n_add p0 ip ip0 env
            else
              env
        )p_rels env


    let fm uf are_eq rclass_of env eqs =
      if debug_fm () then fprintf fmt "[fm] in fm/fm-simplex@.";
      Options.tool_req 4 "TR-Arith-Fm";
      let ineqs =
        MPL.fold (fun k v acc ->
          assert (is_normalized_poly uf v.Oracle.ple0);
          (better_bound_from_intervals env v) :: acc
        ) env.inequations []
      in
      (*let pbs = split_problem env ineqs (fun p -> P.leaves p) in*)
      let pbs = split_problem env ineqs args_of in
      let res = List.fold_left
        (fun (env, eqs) (ineqs, _) ->
          let env = update_linear_dep env rclass_of ineqs in
          let mp = Oracle.MINEQS.add_to_map Oracle.MINEQS.empty ineqs in
          let env, eqs, (x_rels, p_rels) =
            Oracle.available add_inequations are_eq
              (env, eqs, (MX.empty, MP.empty)) mp
          in
          let env = monomes_relational_deductions env x_rels in
          let env = polynomes_relational_deductions env p_rels in
          env, eqs
        )(env, eqs) pbs
      in
      if debug_fm () then fprintf fmt "[fm] out fm/fm-simplex@.";
      res

    let is_num r =
      let ty = X.type_info r in ty == Ty.Tint || ty == Ty.Treal

    let add_disequality are_eq env eqs p expl =
      let ty = P.type_info p in
      match P.to_list p with
      | ([], v) ->
        if Q.sign v = 0 then
          raise (Exception.Inconsistent (expl, env.classes));
	env, eqs
      | ([a, x], v) ->
	let b = Q.div (Q.minus v) a in
	let i1 = I.point b ty expl in
	let i2, use2 =
	  try
	    MX.n_find x env.monomes
	  with Not_found -> I.undefined ty, SX.empty
	in
	let i = I.exclude i1 i2 in
        let env = MX.n_add x (i,use2) i2 env in
	let env = tighten_non_lin are_eq x use2 env expl in
	env, find_eq eqs x i env
      | _ ->
	let p, c, _ = P.normal_form_pos p in
	let i1 = I.point (Q.minus c) ty expl in
	let i2 =
	  try
	    MP.n_find p env.polynomes
	  with Not_found -> I.undefined ty
	in
	let i = I.exclude i1 i2 in
	let env =
	  if I.is_strict_smaller i i2 then
            update_monomes_from_poly p i (MP.n_add p i i2 env)
	  else env
	in
	env, eqs

    let add_equality are_eq env eqs p expl =
      let ty = P.type_info p in
      match P.to_list p with
      | ([], v) ->
        if Q.sign v <> 0 then
	  raise (Exception.Inconsistent (expl, env.classes));
        env, eqs

      | ([a, x], v) ->
	let b = Q.div (Q.minus v) a in
	let i = I.point b ty expl in
        let i2, use =
          try MX.n_find x env.monomes
          with Not_found -> I.undefined ty, SX.empty
        in
	let i = I.intersect i i2 in
        let env = MX.n_add x (i, use) i2 env in
	let env = tighten_non_lin are_eq x use env expl in
	env, find_eq eqs x i env
      | _ ->
	let p, c, _ = P.normal_form_pos p in
	let i = I.point (Q.minus c) ty expl in
	let i, ip =
	  try
	    let ip =  MP.n_find p env.polynomes in
	    I.intersect i ip, ip
	  with Not_found -> i, I.undefined ty
	in
	let env =
	  if I.is_strict_smaller i ip then
            update_monomes_from_poly p i (MP.n_add p i ip env)
	  else env
	in
	let env =
	  { env with
	    known_eqs = SX.add (alien_of p) env.known_eqs
          } in
	env, eqs

    let normal_form a = match a with
      | L.Builtin (false, n, [r1; r2])
          when is_le n && X.type_info r1 == Ty.Tint ->
        let pred_r1 = P.sub (poly_of r1) (P.create [] Q.one Ty.Tint) in
	LR.mkv_builtin true  n  [r2; alien_of pred_r1]

      | L.Builtin (true, n, [r1; r2]) when
	  not (is_le n) && X.type_info r1 == Ty.Tint ->
        let pred_r2 = P.sub (poly_of r2) (P.create [] Q.one Ty.Tint) in
	LR.mkv_builtin true ale [r1; alien_of pred_r2]

      | L.Builtin (false, n, [r1; r2]) when is_le n ->
	LR.mkv_builtin true alt [r2; r1]

      | L.Builtin (false, n, [r1; r2]) when is_lt n ->
	LR.mkv_builtin true ale [r2; r1]

      | _ -> a

    let remove_trivial_eqs eqs la =
      let la =
        List.fold_left (fun m ((a, _, _, _) as e) -> MR.add a e m) MR.empty la
      in
      let eqs, _ =
        List.fold_left
          (fun ((eqs, m) as acc) ((sa, root, ex, orig) as e) ->
            if MR.mem sa m then acc else e :: eqs, MR.add sa e m
          )([], la) eqs
      in
      eqs

    let equalities_from_polynomes env eqs =
      let known, eqs =
        MP.fold
          (fun p i (knw, eqs) ->
            let xp = alien_of p in
            if SX.mem xp knw then knw, eqs
            else
              match I.is_point i with
              | Some (num, ex) ->
                let r2 = alien_of (P.create [] num (P.type_info p)) in
                SX.add xp knw, (LR.mkv_eq xp r2, None, ex, Sig.Other) :: eqs
              | None -> knw, eqs
          ) env.polynomes  (env.known_eqs, eqs)
      in {env with known_eqs= known}, eqs



    let equalities_from_monomes env eqs =
      let known, eqs =
        MX.fold
          (fun x (i,_) (knw, eqs) ->
            if SX.mem x knw then knw, eqs
            else
              match I.is_point i with
              | Some (num, ex) ->
                let r2 = alien_of (P.create [] num (X.type_info x)) in
                SX.add x knw, (LR.mkv_eq x r2, None, ex, Sig.Other) :: eqs
              | None -> knw, eqs
          ) env.monomes  (env.known_eqs, eqs)
      in {env with known_eqs= known}, eqs

    let equalities_from_intervals env eqs =
      let env, eqs = equalities_from_polynomes env eqs in
      equalities_from_monomes env eqs

    let count_splits env la =
      let nb =
        List.fold_left
          (fun nb (_,_,_,i) ->
            match i with
            | CS (Th_arith, n) -> Numbers.Q.mult nb n
            | _ -> nb
          )env.size_splits la
      in
      {env with size_splits = nb}

    let remove_ineq a ineqs =
      match a with None -> ineqs | Some a -> MPL.remove a ineqs

    let add_ineq a v ineqs =
      match a with None -> ineqs | Some a -> MPL.add a v ineqs


    (*** functions to improve intervals modulo equality ***)
    let tighten_eq_bounds env r1 r2 p1 p2 origin_eq expl =
      if P.is_const p1 != None || P.is_const p2 != None then env
      else
        match origin_eq with
        | CS _ | NCS _ -> env
        | Subst | Sig.Other ->
          (* Subst is needed, but is Other needed ?? or is it subsumed ? *)
          let i1, us1, is_mon_1 = generic_find r1 env in
          let i2, us2, is_mon_2 = generic_find r2 env in
          let j = I.add_explanation (I.intersect i1 i2) expl in
          let impr_i1 = I.is_strict_smaller j i1 in
          let impr_i2 = I.is_strict_smaller j i2 in
          Debug.tighten_interval_modulo_eq p1 p2 i1 i2 impr_i1 impr_i2 j;
          let env =
            if impr_i1 then generic_add r1 j us1 is_mon_1 env else env
          in
          if impr_i2 then generic_add r2 j us2 is_mon_2 env else env

    let rec loop_update_intervals are_eq env cpt =
      let cpt = cpt + 1 in
      let env = {env with improved_p=SP.empty; improved_x=SX.empty} in
      let env = update_non_lin_monomes_intervals are_eq env in
      let env = Sim_Wrap.solve env 1 in
      let env = update_polynomes_intervals env in
      let env = Sim_Wrap.solve env 1 in
      if env.improved_p == SP.empty && env.improved_x == SX.empty || cpt > 10
      then env
      else loop_update_intervals are_eq env cpt

    let assume ~query env uf la =
      Oracle.incr_age ();
      let env = count_splits env la in
      let are_eq = Uf.are_equal uf ~added_terms:true in
      let classes = Uf.cl_extract uf in
      let rclass_of = Uf.rclass_of uf in
      let env =
        {env with
          improved_p=SP.empty; improved_x=SX.empty; classes; new_uf = uf}
      in
      Debug.env env;
      let nb_num = ref 0 in
      let env, eqs, new_ineqs, to_remove =
        List.fold_left
	  (fun ((env, eqs, new_ineqs, rm) as acc) (a, root, expl, orig) ->
	    let a = normal_form a in
	    Debug.assume a expl;
	    try
              match a with
	      | L.Builtin(_, n, [r1;r2]) when is_le n || is_lt n ->
                incr nb_num;
		let p1 = poly_of r1 in
		let p2 = poly_of r2 in
		let ineq =
                  Oracle.create_ineq p1 p2 (is_le n) root expl in
                begin
                  match ineq_status ineq with
                  | Bottom -> raise (Exception.Inconsistent (expl, env.classes))
                  | Trivial_eq | Trivial_ineq _ ->
                     {env with inequations=remove_ineq root env.inequations},
                     eqs, new_ineqs,
                    (match root with None -> rm | Some a -> a:: rm)

                  | Monome _
                  | Other ->
		     let env =
		       init_monomes_of_poly
                         are_eq env ineq.Oracle.ple0 SX.empty
                         Explanation.empty
                     in
		     let env =
		       update_ple0
                         are_eq env ineq.Oracle.ple0 (is_le n) expl
                     in
		     {env with inequations=add_ineq root ineq env.inequations},
                     eqs, true, rm
                end

	      | L.Distinct (false, [r1; r2]) when is_num r1 && is_num r2 ->
                 incr nb_num;
		 let p = P.sub (poly_of r1) (poly_of r2) in
                 begin
                   match P.is_const p with
                   | Some c ->
                      if Q.is_zero c then (* bottom *)
                        raise (Exception.Inconsistent (expl, env.classes))
                      else (* trivial *)
                        let rm = match root with Some a -> a::rm | None -> rm in
                        env, eqs, new_ineqs, rm
                   | None ->
		      let env = init_monomes_of_poly are_eq env p SX.empty
                                                     Explanation.empty
                      in
		      let env, eqs = add_disequality are_eq env eqs p expl in
                      env, eqs, new_ineqs, rm
                 end

	      | L.Eq(r1, r2) when is_num r1 && is_num r2 ->
                incr nb_num;
                let p1 = poly_of r1 in
                let p2 = poly_of r2 in
		let p = P.sub p1 p2 in
		let env = init_monomes_of_poly are_eq env p SX.empty
                  Explanation.empty
                in
		let env, eqs = add_equality are_eq env eqs p expl in
                let env = tighten_eq_bounds env r1 r2 p1 p2 orig expl in
                env, eqs, new_ineqs, rm

	      | _ -> acc

	    with I.NotConsistent expl ->
              Debug.inconsistent_interval expl ;
	      raise (Exception.Inconsistent (expl, env.classes))
	  )
	  (env, [], false, []) la

      in
      try
        let env = if query then env else Sim_Wrap.solve env 1 in
        if !nb_num = 0 || query then env, {assume=[]; remove = to_remove}
        else
          (* we only call fm when new ineqs are assumed *)
          let env, eqs =
            if new_ineqs && not (Options.no_fm ()) then
              fm uf are_eq rclass_of env eqs
            else env, eqs
          in
          let env = Sim_Wrap.solve env 1 in
          let env = loop_update_intervals are_eq env 0 in
          let env, eqs = equalities_from_intervals env eqs in

          Debug.env env;
          let eqs = remove_trivial_eqs eqs la in
          Debug.implied_equalities eqs;
          let to_assume =
	    List.rev_map (fun (sa, _, ex, orig) -> (LSem sa, ex, orig)) eqs in
          env, {assume = to_assume; remove = to_remove}
        with I.NotConsistent expl ->
          Debug.inconsistent_interval expl ;
          raise (Exception.Inconsistent (expl, env.classes))


    let assume ~query env uf la =
      let env, res = assume ~query env uf la in
      let polys =
        MP.fold
          (fun p _ mp ->
            if Uf.is_normalized uf (alien_of p) then mp else MP.remove p mp)
          env.polynomes env.polynomes
      in
      {env with polynomes = polys}, res

    let query env uf a_ex =
      try
        ignore(assume ~query:true env uf [a_ex]);
        No
      with Exception.Inconsistent (expl, classes) -> Yes (expl, classes)


    let assume env uf la =
      if Options.timers() then
        try
	  Timers.exec_timer_start Timers.M_Arith Timers.F_assume;
	  let res =assume ~query:false env uf la in
	  Timers.exec_timer_pause Timers.M_Arith Timers.F_assume;
	  res
        with e ->
	  Timers.exec_timer_pause Timers.M_Arith Timers.F_assume;
	  raise e
      else assume ~query:false env uf la

    let query env uf la =
      if Options.timers() then
        try
	  Timers.exec_timer_start Timers.M_Arith Timers.F_query;
	  let res = query env uf la in
	  Timers.exec_timer_pause Timers.M_Arith Timers.F_query;
	  res
        with e ->
	  Timers.exec_timer_pause Timers.M_Arith Timers.F_query;
	  raise e
      else query env uf la

    let case_split_polynomes env =
      let o = MP.fold
        (fun p i o ->
	  match I.finite_size i with
	  | Some s when Q.compare s Q.one > 0 ->
	    begin
	      match o with
	      | Some (s', p', _) when Q.compare s' s < 0 -> o
	      | _ ->
	        let n, ex, is_large = I.borne_inf i in
                assert (is_large);
		Some (s, p, n)
	    end
	  | _ -> o
        ) env.polynomes None in
      match o with
      | Some (s, p, n) ->
        let r1 = alien_of p in
	let r2 = alien_of (P.create [] n  (P.type_info p)) in
        Debug.case_split r1 r2;
	[LR.mkv_eq r1 r2, true, CS (Th_arith, s)], s
      | None ->
        Debug.no_case_split "polynomes";
	[], Q.zero

    let case_split_monomes env =
      let o = MX.fold
        (fun x (i,_) o ->
	  match I.finite_size i with
	  | Some s when Q.compare s Q.one > 0 ->
	    begin
	      match o with
	      | Some (s', _, _) when Q.compare s' s < 0 -> o
	      | _ ->
                let n, ex, is_large = I.borne_inf i in
                assert (is_large);
		Some (s, x, n)
	    end
	  | _ -> o
        ) env.monomes None in
      match o with
      | Some (s,x,n) ->
        let ty = X.type_info x in
        let r1 = x in
	let r2 = alien_of (P.create [] n  ty) in
        Debug.case_split r1 r2;
	[LR.mkv_eq r1 r2, true, CS (Th_arith, s)], s
      | None ->
        Debug.no_case_split "monomes";
	[], Q.zero

    let check_size for_model env res =
      if for_model then res
      else
        match res with
        | [] -> res
        | [_, _, CS (Th_arith, s)] ->
          if Numbers.Q.compare (Q.mult s env.size_splits) (max_split ()) <= 0 ||
	    Numbers.Q.sign  (max_split ()) < 0 then res
          else []
        | _ -> assert false

    let default_case_split env uf ~for_model =
      Options.tool_req 4 "TR-Arith-CaseSplit";
      match check_size for_model  env (Sim_Wrap.case_split env uf) with
        [] ->
          begin
            let cs1, sz1 = case_split_polynomes env in
            let cs2, sz2 =  case_split_monomes env in
            match check_size for_model env cs1, check_size for_model env cs2
            with
            | [], cs | cs, []  -> cs
            | cs1, cs2 -> if Q.compare sz1 sz2 < 0 then cs1 else cs2
          end
      | res -> res

    let add =
      let are_eq t1 t2 =
        if Term.equal t1 t2 then Yes (Explanation.empty, []) else No
      in
      fun env new_uf r t ->
        try
          let env = {env with new_uf} in
          if is_num r then
            init_monomes_of_poly are_eq env
              (poly_of r) SX.empty Explanation.empty
          else env
        with I.NotConsistent expl ->
          Debug.inconsistent_interval expl ;
          raise (Exception.Inconsistent (expl, env.classes))

(*
    let extract_improved env =
      SP.fold
        (fun p acc ->
	  MP.add p (MP.find p env.polynomes) acc)
        env.improved MP.empty
*)

    let print_model fmt env rs = match rs with
      | [] -> ()
      | _ ->
	fprintf fmt "Relation:";
        List.iter (fun (t, r) ->
          let p = poly_of r in
          let ty = P.type_info p in
          if ty == Ty.Tint || ty == Ty.Treal then
	    let p', c, d = P.normal_form_pos p in
	    let pu' =
	      try MP.n_find p' env.polynomes
	      with Not_found -> I.undefined ty
	    in
	    let pm' =
	      try intervals_from_monomes ~monomes_inited:false env p'
	      with Not_found -> I.undefined ty
	    in
	    let u' = I.intersect pu' pm' in
	    if I.is_point u' == None && I.is_undefined u' then
	      let u =
	        I.scale d
	          (I.add u'
		     (I.point c ty Explanation.empty)) in
	      fprintf fmt "\n %a ∈ %a" Term.print t I.pretty_print u
        ) rs;
        fprintf fmt "\n@."

    let new_terms env = Term.Set.empty

    let case_split_union_of_intervals =
      let aux acc uf i z =
        if Uf.is_normalized uf z then
          match I.bounds_of i with
          | [] -> assert false
          | [_] -> ()
          | (_,(v, ex))::_ -> acc := Some (z, v, ex); raise Exit
      in fun env uf ->
        let cs = ref None in
        try
          MP.iter (fun p i -> aux cs uf i (alien_of p)) env.polynomes;
          MX.iter (fun x (i,_) -> aux cs uf i x) env.monomes;
          []
        with Exit ->
          match !cs with
          | None -> assert false
          | Some(_,None, _) -> assert false
          | Some(r1,Some (n, eps), ex) ->
            let ty = X.type_info r1 in
            let r2 = alien_of (P.create [] n ty) in
            let pred =
              if Q.is_zero eps then ale else (assert (Q.is_m_one eps); alt)
            in
            [LR.mkv_builtin true pred [r1; r2], true, CS (Th_arith, Q.one)]


    (*****)

    let int_constraints_from_map_intervals =
      let aux p xp i uf acc =
        if Uf.is_normalized uf xp && I.is_point i == None
          && P.type_info p == Ty.Tint
        then (p, I.bounds_of i) :: acc
        else acc
      in
      fun env uf ->
        let acc =
          MP.fold (fun p i acc -> aux p (alien_of p) i uf acc) env.polynomes []
        in
        MX.fold (fun x (i,s) acc -> aux (poly_of x) x i uf acc) env.monomes acc


    let fm_simplex_unbounded_integers_encoding env uf =
      let simplex = Sim.Core.empty ~is_int:true ~check_invs:true ~debug:0 in
      let int_ctx = int_constraints_from_map_intervals env uf in
      List.fold_left
        (fun simplex (p, uints) ->
          match uints with
          | [] ->
            fprintf fmt "Intervals already empty !!!!@.";
            assert false
          | _::_::_ ->
            fprintf fmt "case-split over unions of intervals is needed !!!!@.";
            assert false

          | [(mn, ex_mn), (mx, ex_mx)] ->
            let l, c = P.to_list p in
            let l = List.rev_map (fun (c, x) -> x, c) (List.rev l) in
            assert (Q.sign c = 0);
            let cst0 =
              List.fold_left (fun z (x, c) -> Q.add z (Q.abs c))Q.zero l
            in
            let cst = Q.div cst0 (Q.from_int 2) in
            assert (mn == None || mx == None);
            let mn =
              match mn with
              | None -> None
              | Some (q, q') -> Some (Q.add q cst, q')
            in
            let mx =
              match mx with
              | None -> None
              | Some (q, q') -> Some (Q.sub q cst, q')
            in
            match l with
            | [] -> assert false
            | [x, c] ->
              assert (Q.is_one c);
              Sim.Assert.var simplex x mn ex_mn mx ex_mx |> fst
            | _ ->
              let xp = alien_of p in
              let sim_p =
                match Sim.Core.poly_of_slake simplex xp with
                | Some res -> res
                | None -> Sim.Core.P.from_list l
              in
              Sim.Assert.poly simplex sim_p xp mn ex_mn mx ex_mx |> fst

        ) simplex int_ctx


    let round_to_integers list =
      List.rev_map (fun (x, q1) ->
        let f = Q.floor q1 in
        let c = Q.ceiling q1 in
        x, if Q.compare (Q.sub q1 f) (Q.sub c q1) > 0 then f else c
      ) (List.rev list)


    (* cannot replace directly with env.int_sim because of encoding *)
    let model_from_simplex sim is_int env uf =
      match Sim.Result.get None sim with
      | Sim.Core.Unknown | Sim.Core.Unbounded _ | Sim.Core.Max _ -> assert false

      | Sim.Core.Unsat ex ->
        (* when splitting on union of intervals, FM does not include
           related ineqs when crossing. So, we may miss some bounds/deductions,
           and FM-Simplex may fail to find a model *)
        raise (Exception.Inconsistent(Lazy.force ex, env.classes))

      | Sim.Core.Sat sol ->
        let {Sim.Core.main_vars; slake_vars; int_sol} = Lazy.force sol in
        let main_vars, slake_vars =
          if int_sol || not is_int then main_vars, slake_vars
          else round_to_integers main_vars, round_to_integers slake_vars
        in
      let fct = if is_int then Term.int else Term.real in
      List.fold_left
        (fun acc (v, q) ->
          assert (not is_int || Q.is_int q);
          if SX.mem v env.known_eqs || not (Uf.is_normalized uf v) then
            (* may happen because of incremental simplex on rationals *)
            acc
          else
            let t = fct (Q.to_string q) in
            let r, _ = X.make t in
            if debug_interpretation() then
              fprintf fmt "[%s simplex] %a = %a@."
                (if is_int then "integer" else "rational") X.print v X.print r;
            (v, r, Explanation.empty) :: acc
        )[] (List.rev main_vars)


    let model_from_unbounded_domains =
      let mk_cs acc (x, v, ex) =
        ((LR.view (LR.mk_eq x v)), true, CS (Th_arith, Q.from_int 2)) :: acc
      in
      fun env uf ->
        assert (env.int_sim.Sim.Core.status == Sim.Core.SAT);
        assert (env.rat_sim.Sim.Core.status == Sim.Core.SAT);
        let rat_sim = env.rat_sim in (* reuse existing rat_sim *)
        let int_sim = (* create a new int_sim with FM-Simplex encoding *)
          let sim = fm_simplex_unbounded_integers_encoding env uf in
          Sim.Solve.solve sim
        in
        let l1 = model_from_simplex rat_sim false env uf in
        let l2 = model_from_simplex int_sim true  env uf in
        List.fold_left mk_cs (List.fold_left mk_cs [] l1) l2


    let case_split env uf ~for_model =
      let res = default_case_split env uf for_model in
      match res with
      | [] ->
        if not for_model then []
        else
          begin
            match case_split_union_of_intervals env uf with
            | [] -> model_from_unbounded_domains env uf
            | l -> l
          end
      | _ -> res


    (*** part dedicated to FPA reasoning ************************************)

    let best_interval_of optimized env p =
      (* p is supposed to be in normal_form_pos *)
      match P.is_const p with
      | Some c -> env, I.point c (P.type_info p) Explanation.empty
      | None ->
        let i =
          try let i, _, _ = generic_find (alien_of p) env in i
          with Not_found -> I.undefined (P.type_info p)
        in
        if SP.mem p !optimized then env, i
        else
          try
            let j = Sim_Wrap.infer_best_bounds env p in
            optimized := SP.add p !optimized;
            let k = I.intersect i j in
            if not (I.is_strict_smaller k i) then env, i
            else
              let env = MP.n_add p k i env in
              Sim_Wrap.solve env 1, k
          with I.NotConsistent expl ->
            if true (*debug_fpa() >= 2*) then begin
              [@ocaml.ppwarning "TODO: find an example triggering this case!"]
                fprintf fmt "TODO: should check that this is correct !!!!@."
            end;
	    raise (Exception.Inconsistent (expl, env.classes))

    let mk_const_term ty s =
      match ty with
      | Ty.Tint -> Term.int (Q.to_string s)
      | Ty.Treal -> Term.real (Q.to_string s)
      | _ -> assert false

    let integrate_mapsTo_bindings sbs maps_to =
      try
        let sbs =
          List.fold_left
            (fun ((sbt, sty) as sbs) (x, tx) ->
              let x = Sy.Var x in
              assert (not (Symbols.Map.mem x sbt));
              let t = Term.apply_subst sbs tx in
              let mk, _ = X.make t in
              match P.is_const (poly_of mk) with
              | None ->
                if debug_fpa() >= 2 then begin
                  fprintf fmt "bad semantic trigger %a |-> %a"
                    Sy.print x Term.print tx;
                  fprintf fmt " left-hand side is not a constant!@.";
                end;
                raise Exit
              | Some c ->
                let tc = mk_const_term (Term.type_info t) c in
                Symbols.Map.add x tc sbt, sty
            )sbs maps_to
        in
        Some sbs
      with Exit -> None

    let extend_with_domain_substitution =
      (* TODO : add the ability to modify the value of epsilon ? *)
      let eps = Q.div_2exp Q.one 1076 in
      let aux idoms sbt =
        Hstring.Map.fold
          (fun hs (lv, uv, ty) sbt ->
            let s = Hstring.view hs in
	    match s.[0] with
	    | '?' -> sbt
	    | _ ->
              let lb_var = Sy.var s in
              let lb_val = match lv, uv with
	        | None, None -> raise Exit
                | Some (q1, false), Some (q2, false) when Q.equal q1 q2 ->
		  mk_const_term ty q1

                | Some (q1,s1), Some (q2,s2) ->
                  fprintf fmt "%a <= %a <= %a@."
                    Q.print q1 Sy.print lb_var Q.print q2;
                  Format.eprintf "Which value should we choose ?@.";
                  assert (Q.compare q2 q1 >= 0);
                  assert false

                | Some (q, is_strict), None -> (* hs > q or hs >= q *)
                  mk_const_term ty (if is_strict then Q.add q eps else q)

                | None, Some (q, is_strict) -> (* hs < q or hs <= q *)
                  mk_const_term ty (if is_strict then Q.sub q eps else q)
              in
	      Sy.Map.add lb_var lb_val sbt
          ) idoms sbt
      in
      fun (sbt, sbty) idoms ->
        try Some (aux idoms sbt, sbty)
        with Exit ->
          if debug_fpa() >=2 then
            fprintf fmt "[IC] extend_with_domain_substitution failed !@.";
          None

    let terms_linear_dep {linear_dep} lt =
      match lt with
      | [] | [_] -> true
      | e::l ->
        try
          let st = MT.find e linear_dep in
          List.for_all (fun t -> ST.mem t st) l
        with Not_found -> false

    exception Sem_match_fails of t

    let domain_matching lem_name tr sbt env uf optimized =
      try
        let idoms, maps_to, env, uf =
          List.fold_left
            (fun (idoms, maps_to, env, uf) s ->
              match s with
              | F.MapsTo (x, t) ->
                (* this will be done in the latest phase *)
                idoms, (x, t) :: maps_to, env, uf

              | F.Interval (t, lb, ub) ->
                let tt = Term.apply_subst sbt t in
                assert (Term.is_ground tt);
                let uf, _ = Uf.add uf tt in
	        let rr, ex = Uf.find uf tt in
	        let p = poly_of rr in
	        let p', c', d = P.normal_form_pos p in
	        let env, i' = best_interval_of optimized env p' in
                let ic = I.point c' (P.type_info p') Explanation.empty in
                let i = I.scale d (I.add i' ic) in
                begin match I.match_interval lb ub i idoms with
                | None -> raise (Sem_match_fails env)
                | Some idoms -> idoms, maps_to, env, uf
                end

              | F.NotTheoryConst t ->
                let tt = Term.apply_subst sbt t in
                let uf, _ = Uf.add uf tt in
                if X.leaves (fst (Uf.find uf tt)) == [] ||
                  X.leaves (fst (X.make tt)) == [] then
                  raise (Sem_match_fails env);
                idoms, maps_to, env, uf

              | F.IsTheoryConst t ->
                let tt = Term.apply_subst sbt t in
                let uf, _ = Uf.add uf tt in
                let r, _ = X.make tt in
                if X.leaves r != [] then raise (Sem_match_fails env);
                idoms, maps_to, env, uf

              | F.LinearDependency (x, y) ->
                let x = Term.apply_subst sbt x in
                let y = Term.apply_subst sbt y in
                if not (terms_linear_dep env [x;y]) then
                  raise (Sem_match_fails env);
                let uf, _ = Uf.add uf x in
                let uf, _ = Uf.add uf y in
                idoms, maps_to, env, uf
            )(Hstring.Map.empty, [], env, uf) tr.F.semantic
        in
        env, Some (idoms, maps_to)
      with Sem_match_fails env -> env, None


    let semantic_matching lem_name tr sbt env uf optimized =
      match domain_matching lem_name tr sbt env uf optimized with
      | env, None -> env, None
      | env, Some(idom, mapsTo) ->
        begin match extend_with_domain_substitution sbt idom with
        | None -> env, None
        | Some sbs -> env, integrate_mapsTo_bindings sbs mapsTo
        end

    let record_this_instance f accepted lorig =
      if Options.profiling() then
        match F.view lorig with
        | F.Lemma {F.name;loc} -> Profiling.new_instance_of name f loc accepted
        | _ -> assert false

    let profile_produced_terms menv lorig nf s trs =
      if Options.profiling() then
        let st0 =
          List.fold_left (fun st t -> Term.subterms st (Term.apply_subst s t))
            Term.Set.empty trs
        in
        let name, loc, f = match F.view lorig with
          | F.Lemma {F.name;main;loc} -> name, loc, main
          | _ -> assert false
        in
        let st1 = F.ground_terms_rec nf in
        let diff = Term.Set.diff st1 st0 in
        let info, _ = EM.terms_info menv in
        let _new = Term.Set.filter (fun t -> not (MT.mem t info)) diff in
        Profiling.register_produced_terms name loc st0 st1 diff _new

    let new_facts_for_axiom
        ~do_syntactic_matching menv uf selector optimized substs accu =
      List.fold_left
        (fun acc ({trigger_formula=f; trigger_age=age; trigger_dep=dep;
                   trigger_orig=orig; trigger = tr}, subst_list) ->
          List.fold_left
	    (fun (env, acc)
	      {sbs = sbs;
	       sty = sty;
	       gen = g;
	       goal = b;
	       s_term_orig = torig;
	       s_lem_orig = lorig} ->
                (*
                  Here, we'll try to extends subst 's' to conver variables
                  appearing in semantic triggers
                *)
                let lem_name = F.name_of_lemma orig in
                let s = sbs, sty in
                if debug_fpa () >= 2 then begin
                  fprintf fmt "[IC] try to extend synt sbt %a of ax %a@."
                    (Term.Subst.print Term.print) sbs F.print orig;
                end;
	        match tr.F.guard with
	        | Some a -> assert false (*guards not supported for TH axioms*)

                | None when tr.F.semantic == [] && not do_syntactic_matching ->
                  (* pure syntactic insts already generated *)
                  env, acc

	        | None when not (terms_linear_dep env torig) ->
		  if debug_fpa () >= 2 then
		    fprintf fmt "semantic matching failed(1)@.";
                  env, acc

                | None ->
		  match semantic_matching lem_name tr s env uf optimized with
		  | env, None ->
		    if debug_fpa () >= 2 then
		      fprintf fmt "semantic matching failed(2)@.";
                    env, acc
		  | env, Some sbs ->
		    if debug_fpa () >= 2 then
		      fprintf fmt "semantic matching succeeded:@.%a@."
			(Term.Subst.print Term.print) (fst sbs);
		    let nf = F.apply_subst sbs f in
                    let accepted = selector nf orig in
                    record_this_instance nf accepted lorig;
                    if accepted then begin
                      let hyp =
                        List.map (fun f -> F.apply_subst sbs f) tr.F.hyp
                      in
		      let p =
			{ F.f = nf;
                          origin_name = F.name_of_lemma lorig;
                          trigger_depth = tr.F.depth;
                          gdist = -1;
                          hdist = -1;
                          nb_reductions = 0;
		          age = 1+(max g age);
		          mf = true;
		          gf = b;
		          lem = Some lorig;
		          from_terms = torig;
                             (* does'nt work if a 'gf' with theory_elim = true
                                was already assumed in the SAT !!! *)
                          theory_elim = false;
			}
		      in
                      profile_produced_terms menv lorig nf s tr.F.content;
                      let dep =
                        if not (Options.proof() || Options.profiling())
                        then
                          dep
                        else Ex.union dep (Ex.singleton (Ex.Dep lorig))
                      in
		      env, (hyp, p, dep) :: acc
                    end
                    else (* instance not 'accepted' *)
                      env, acc
	    ) acc subst_list
        ) accu substs


    let syntactic_matching menv env uf selector =
      let synt_match =
        MF.fold
          (fun f th_ax accu ->
            (* currently, No diff between propagators and case-split axs *)
            let forms = MF.singleton f (0 (*0 = age *), Ex.empty) in
            let menv = EM.add_triggers ~backward:Util.Normal menv forms in
            let res = EM.query menv uf in
            if debug_fpa () >= 2 then begin
              let cpt = ref 0 in
              List.iter (fun (_, l) -> List.iter (fun _ -> incr cpt) l) res;
	      fprintf fmt "syntactic matching of Ax %s: got %d substs@."
                (F.name_of_lemma f) !cpt
            end;
            res:: accu
          )env.th_axioms []
      in
      {env with syntactic_matching = synt_match}

    let instantiate ~do_syntactic_matching match_terms env uf selector =
      if debug_fpa () >= 2 then fprintf fmt "entering IC.instantiate@.";
      let optimized = ref (SP.empty) in
      let t_infos, t_subterms = match_terms in
      let menv = EM.make ~max_t_depth:100 t_infos t_subterms [] in
      let env =
        if not do_syntactic_matching then env
        else syntactic_matching menv env uf selector
      in
      let env, insts =
        List.fold_left
        (fun accu substs ->
          new_facts_for_axiom
            ~do_syntactic_matching menv uf selector optimized substs accu
        )(env, []) env.syntactic_matching
      in
      if debug_fpa () >= 2 then
	fprintf fmt "IC.instantiate: %d insts generated@." (List.length insts);
      env, insts


    let separate_semantic_triggers =
      let not_theory_const = Hstring.make "not_theory_constant" in
      let is_theory_const = Hstring.make "is_theory_constant" in
      let linear_dep = Hstring.make "linear_dependency" in
      fun th_form ->
        let {F.triggers} as q =
          match F.view th_form with F.Lemma q -> q | _ -> assert false
        in
        let r_triggers =
          List.rev_map
            (fun tr ->
              (* because sem-triggers will be set by theories *)
              assert (tr.F.semantic == []);
              let syn, sem =
                List.fold_left
                  (fun (syn, sem) t ->
                    match Term.view t with
                    | {Term.f=Symbols.In (lb, ub); xs=[x]} ->
                      syn, (F.Interval (x, lb, ub)) :: sem

                    | {Term.f=Symbols.MapsTo x; xs=[t]} ->
                      syn, (F.MapsTo (x, t)) :: sem

                    | {Term.f=Sy.Name(hs,_); xs=[x]}
                        when Hstring.equal hs not_theory_const ->
                      syn, (F.NotTheoryConst x) :: sem

                    | {Term.f=Sy.Name(hs,_); xs=[x]}
                        when Hstring.equal hs is_theory_const ->
                      syn, (F.IsTheoryConst x) :: sem

                    | {Term.f=Sy.Name(hs,_); xs=[x;y]}
                        when Hstring.equal hs linear_dep ->
                      syn, (F.LinearDependency(x,y)) :: sem

                    | _ -> t::syn, sem
                  )([], []) (List.rev tr.F.content)
              in
              {tr with F.content = syn; semantic = sem}
            )triggers
        in
        F.mk_forall
          q.F.name q.F.loc q.F.binders (List.rev r_triggers) q.F.main
          (F.id th_form) (Some (q.F.free_v, q.F.free_vty))

    let assume_th_elt t th_elt =
      let {Commands.axiom_kind; th_form; th_name; extends} = th_elt in
      let kd_str =
        if axiom_kind == Parsed.Propagator then "Th propagator" else "Th CS"
      in
      match extends with
      | Typed.NIA | Typed.NRA | Typed.FPA ->
        if EM.unused_context th_form then begin
          if debug_fpa () >= 2 then
            fprintf fmt "[IC][Theory %s][%s] %a not in used-context. Ignore@."
              th_name kd_str F.print th_form;
          t
        end
        else begin
          let th_form = separate_semantic_triggers th_form in
          let th_elt = {th_elt with Commands.th_form} in
          if debug_fpa () >= 2 then
            fprintf fmt "[IC][Theory %s][%s] %a@."
              th_name kd_str F.print th_form;
          assert (not (MF.mem th_form t.th_axioms));
          {t with th_axioms = MF.add th_form th_elt t.th_axioms}
        end
      | _ -> t

    let retrieve_used_context {th_axioms} dep =
      let deps = Ex.formulas_of dep in
      let used, unused =
        Formula.Set.fold
          (fun f ((used, assumed) as acc) ->
            if MF.mem f th_axioms then f :: used, MF.remove f assumed else acc
          ) deps ([], th_axioms)
      in
      let unused = MF.fold (fun f _ acc -> f::acc) unused [] in
      used, unused

    let instantiate ~do_syntactic_matching env uf selector =
      if Options.timers() then
        try
	  Timers.exec_timer_start Timers.M_Arith Timers.F_instantiate;
	  let res = instantiate ~do_syntactic_matching env uf selector in
	  Timers.exec_timer_pause Timers.M_Arith Timers.F_instantiate;
	  res
        with e ->
	  Timers.exec_timer_pause Timers.M_Arith Timers.F_instantiate;
	  raise e
      else instantiate ~do_syntactic_matching env uf selector

  end
