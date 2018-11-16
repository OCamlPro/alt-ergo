(******************************************************************************)
(*                                                                            *)
(*     Alt-Ergo: The SMT Solver For Software Verification                     *)
(*     Copyright (C) 2013-2018 --- OCamlPro SAS                               *)
(*                                                                            *)
(*     This file is distributed under the terms of the license indicated      *)
(*     in the file 'License.OCamlPro'. If 'License.OCamlPro' is not           *)
(*     present, please contact us to clarify licensing.                       *)
(*                                                                            *)
(******************************************************************************)

open AltErgoLib
open Format
open Options

module Q = Numbers.Q

module Container : Inequalities.Container_SIG = struct
  module Make
      (X : Sig.X)
      (Uf : Uf.S with type r = X.r)
      (P : Polynome.EXTENDED_Polynome with type r = X.r)
    : Inequalities.S with module P = P = struct

    module FM = Inequalities.FM(X)(Uf)(P)

    include FM
    (* Only redefine functions "available" and "fmSimplex" functions *)

    open Simplex

    let dsimplex = ref false

    module SCache =
      Simplex_cache.MAKE(
      struct
        type t = X.r
        let compare = X.hash_cmp
        include X
      end)

    module MX = Map.Make(struct type t = X.r let compare = X.hash_cmp end)

    module Ex = Exception


    let print_couple fmt (re, eps) =
      fprintf fmt "(%s , %s)" (Q.to_string re) (Q.to_string eps)

    let print_answer (vof,vals) =
      fprintf fmt "vof = %a@." print_couple vof;
      fprintf fmt "@.assignement returned by the Simplex@.";
      List.iter
        (fun (l,v) ->
           fprintf fmt "  L(%d) -> %a@." l print_couple v
        )vals

    let print_parsed_answer answer =
      if debug_fm() then
        match answer with
        | Unsat {vof=vof;vals=vals} ->
          fprintf fmt "I read: the simplex problem is not feasible (<=)@.";
          print_answer (vof,vals)
        | Eq_unsat ->
          fprintf fmt "I read: the simplex problem is not feasible (=)@."
        | Unbound {vof=vof;vals=vals} ->
          fprintf fmt "I read: the simplex problem is not bounnded@.";
          print_answer (vof,vals)
        | Max {vof=vof;vals=vals}  ->
          fprintf fmt "I read: the simplex problem has a solution@.";
          print_answer (vof,vals)

    let add_to_sum ld sum l_m =
      List.fold_left
        (fun sum (c, x) ->
           let lp, ln = try MX.find x sum  with Not_found -> [], [] in
           if Q.sign c > 0 then MX.add x ((ld, c) :: lp, ln) sum
           else MX.add x (lp, (ld, c) :: ln) sum
        ) sum l_m

    let generalized_fm_projection (constrs : (int * t) list) =
      List.fold_left
        (fun (sum, ctt, lds) (ld, ineq) ->
           let l_m, c = P.to_list ineq.ple0 in
           assert (Q.is_int c);
           if l_m == [] then begin
             fprintf fmt "%a <= 0@." P.print ineq.ple0;
             assert false
           end
           else
             let sum = add_to_sum ld sum l_m in
             let ctt = (ld, c) :: ctt in
             let lds = (ld, Q.one) :: lds in
             sum, ctt, lds
        )(MX.empty,[],[]) constrs

    let polynomials_bounding_pb sum ctt lambdas =
      let vars_elim_eqs =
        MX.fold (fun x (l1,l2) acc -> (x,(l1,l2, Q.zero)) :: acc) sum [] in
      let lds_gt_z = lambdas in
      ctt, vars_elim_eqs, lds_gt_z

    let monomial_bounding_pb sum ctt lambdas x sum_x is_pos =
      let max_ctt, vars_elim, s_neq =
        polynomials_bounding_pb sum ctt lambdas in
      let lp, ln = sum_x in
      let coef_x =(x, (lp, ln, if is_pos then Q.m_one else Q.one)) in
      max_ctt, coef_x :: vars_elim, s_neq

    let explain vals constrs =
      List.fold_left
        (fun expl (ld, (re,eps)) ->
           if Q.compare re Q.zero = 0 &&
              Q.compare eps Q.zero = 0 then expl (* XXX eps ? re ? *)
           else
             let {expl=ex} = List.assoc ld constrs in
             Explanation.union expl ex
        )Explanation.empty vals

    let cpt = ref 0

    let tighten_polynomials
        add_ineqs are_eq acc sum ctt lambdas nb_constrs constrs =
      let max_ctt, equas, s_neq = polynomials_bounding_pb sum ctt lambdas in
      let r_max_ctt,r_equas,r_s_neq = SCache.make_repr max_ctt equas s_neq in
      let sim_res =
        match SCache.already_registered r_max_ctt r_equas r_s_neq with
        | None ->
          if !dsimplex then fprintf fmt "Simplex poly in@.";
          incr cpt;
          if !dsimplex then fprintf fmt "new simplex %d@." !cpt;
          let res = Simplex_Q.main max_ctt equas s_neq nb_constrs in
          if !dsimplex then fprintf fmt "Simplex poly out@.";
          SCache.register r_max_ctt r_equas r_s_neq !cpt res ;
          res
        | Some (n, res, ctt') ->
          if SCache.MI.compare Q.compare r_max_ctt ctt' = 0 then begin
            if !dsimplex then fprintf fmt "reuse RESULTS of simplex %d@." n;
            res
          end
          else begin
            if !dsimplex then fprintf fmt "reuse  simplex %d@." n;
            let res = Simplex_Q.partial_restart res max_ctt in
            res
          end
      in
      print_parsed_answer sim_res;
      match sim_res with
      | Unsat _  | Eq_unsat -> acc
      | Unbound {vof=vof;vals=vals} ->
        raise (Ex.Inconsistent (explain vals constrs, []))
      | Max {vof=(re, eps);vals=vals} -> (* XXX: parties reelles nulles *)
        assert (Q.is_zero re);
        let expl = explain vals constrs in
        let cmp = Q.compare eps Q.zero in
        if cmp > 0 then raise(Ex.Inconsistent (expl, []));
        let dep =
          List.fold_left
            (fun dep (ld,(re_ld, eps_ld)) ->
               assert (Q.is_zero re_ld);
               if Q.is_zero eps_ld then dep
               else
                 let ineq = List.assoc ld constrs in
                 match Util.MI.bindings ineq.dep with
                   [a, (n,p, is_le)] ->
                   assert (Q.is_one n && is_le);
                   assert (not (Util.MI.mem a dep));
                   Util.MI.add a (eps_ld, p, is_le) dep
                 | _ -> assert false
            )Util.MI.empty vals
        in
        let ineq =
          {
            ple0 = P.create [] eps Ty.Tint;
            is_le = true; (* add an assert *)
            age = current_age();
            expl = expl;
            dep = dep;
          }
        in
        add_ineqs are_eq acc None [ineq]

    let tighten_monomial
        add_ineqs are_eq acc x sum_x is_pos sum ctt lambdas nb_constrs constrs
      =
      if false || debug_fm() then fprintf fmt "tighten_monomial %s%a@."
          (if is_pos then "+" else "-") X.print x;
      let max_ctt, equas, s_neq =
        monomial_bounding_pb sum ctt lambdas x sum_x is_pos in
      let r_max_ctt,r_equas,r_s_neq = SCache.make_repr max_ctt equas s_neq in
      let sim_res =
        match SCache.already_registered_mon x r_max_ctt r_equas r_s_neq with
        | None ->
          if !dsimplex then fprintf fmt "Simplex monomes in@.";
          incr cpt;
          if !dsimplex then fprintf fmt "new simplex %d@." !cpt;
          let res = Simplex_Q.main max_ctt equas s_neq nb_constrs in
          if !dsimplex then fprintf fmt "Simplex monomes out@.";
          SCache.register_mon x r_max_ctt r_equas r_s_neq !cpt res ;
          res
        | Some (n, res, ctt') ->
          if SCache.MI.compare Q.compare r_max_ctt ctt' = 0 then begin
            if !dsimplex then fprintf fmt "reuse RESULTS of simplex %d@." n;
            res
          end
          else begin
            if !dsimplex then fprintf fmt "reuse  simplex %d@." n;
            let res = Simplex_Q.partial_restart res max_ctt in
            res
          end
      in
      print_parsed_answer sim_res;
      match sim_res with
      | Unsat _ | Eq_unsat -> acc
      | Unbound {vof=vof;vals=vals} ->
        raise (Ex.Inconsistent (explain vals constrs, []))
      | Max {vof=vof,eps; vals=vals} -> (* XXX: parties avec eps nulles *)
        assert (Q.is_zero eps);
        let expl = explain vals constrs in
        let dep =
          List.fold_left
            (fun dep (ld,(re_ld, eps_ld)) ->
               assert (Q.is_zero eps_ld);
               if Q.is_zero re_ld then dep
               else
                 let ineq = List.assoc ld constrs in
                 match Util.MI.bindings ineq.dep with
                   [a, (n,p, is_le)] ->
                   assert (Q.is_one n && is_le);
                   assert (not (Util.MI.mem a dep));
                   Util.MI.add a (re_ld, p, is_le) dep
                 | _ -> assert false
            )Util.MI.empty vals
        in
        let mon_coef = if is_pos then Q.one else Q.m_one in
        let ineq =
          {
            ple0 = P.create [mon_coef, x] vof Ty.Tint;
            is_le = true; (* add an assert *)
            age = current_age();
            expl = expl;
            dep = dep;
          }
        in
        add_ineqs are_eq acc None [ineq]

    let tighten_monomials add_ineqs are_eq acc sum ctt lds nb_ctrs ctrs =
      MX.fold
        (fun x sum_x acc ->
           let sum = MX.remove x sum in
           let acc =
             tighten_monomial
               add_ineqs are_eq acc x sum_x true  sum ctt lds nb_ctrs ctrs in
           let acc =
             tighten_monomial
               add_ineqs are_eq acc x sum_x false sum ctt lds nb_ctrs ctrs in
           acc
        )sum acc

    let fm_simplex add_ineqs are_eq acc constrs nb_constrs =
      if debug_fm() then
        begin
          fprintf fmt "begin fm-simplex: nb_constrs = %d@." nb_constrs;
          List.iter
            (fun (id, {ple0}) ->
               fprintf fmt "%d) %a <= 0@." id P.print ple0) constrs;
        end;
      let sum, ctt, lambdas = generalized_fm_projection constrs in
      let acc =
        if MX.is_empty sum then acc
        else
          let acc =
            tighten_polynomials
              add_ineqs are_eq acc sum ctt lambdas nb_constrs constrs in
          if  Options.tighten_vars() then
            tighten_monomials
              add_ineqs are_eq acc sum ctt lambdas nb_constrs constrs
          else acc
      in
      if debug_fm() then fprintf fmt "end fm-simplex@.@.";
      acc

    let list_of_mineqs mp =
      let nb_ineqs = MP.cardinal mp in
      let cpt = ref (nb_ineqs + 1) in
      let ctrs =
        MINEQS.fold
          (fun p (ineq, _) ctrs ->
             decr cpt;
             (!cpt, ineq) :: ctrs
          )mp []
      in
      ctrs, nb_ineqs

    (*------------------------------------------------------------------------*)

    let is_rat_poly p = match P.type_info p with
      | Ty.Tint -> false
      | Ty.Treal -> true
      | _ -> assert false

    let check_is_rat mp =
      let is_rat = ref true in
      begin
        try MINEQS.iter (fun p i ->  is_rat := is_rat_poly p; raise Exit) mp
        with Exit -> ()
      end;
      let is_rat = !is_rat in
      assert
        (MINEQS.fold (fun p _ z -> z && is_rat == is_rat_poly p) mp true);
      is_rat

    let fmSimplex add_ineqs are_eq acc mp =
      if check_is_rat mp then fourierMotzkin add_ineqs are_eq acc mp
      else
        let constrs, nb_constrs = list_of_mineqs mp in
        fm_simplex add_ineqs are_eq acc constrs nb_constrs

    let available = fmSimplex

  end
end

let () =
  Inequalities.set_current
    (module Container : Inequalities.Container_SIG)

