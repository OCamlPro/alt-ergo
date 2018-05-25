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

open Options
open Format
module Ex = Explanation
module Hs = Hstring
module A = Literal
module SA = Literal.LT.Set
module F = Formula
module SF = Formula.Set

module Pur_Literal_PP = struct

  let eq = Hs.make "="

  module SH = Hs.Set

  let replace_with_true l pos neg =
    let open A in
    let view,is_neg = A.LT.atom_view l in
    match view with
    | EQ _ | EQ_LIST _ ->
      SH.mem eq pos || SH.mem eq neg
    | BT (hs,l) ->
      false
    | PR t ->
      match Term.view t with
      | {Term.f=Symbols.Name(hs,_)} ->
      SH.mem hs pos || SH.mem hs neg
      | _ -> false

  let get_lits gf (pos,neg) =
    let open A in
    let lits = F.atoms_rec false gf.F.f SA.empty in
    SA.fold (fun l (pos,neg) ->
        let view,is_neg = A.LT.atom_view l in
        match view with
        | EQ _ | EQ_LIST _ ->
           pos,neg
          (* if is_neg then
           *   pos, SH.add eq neg
           * else
           *   SH.add eq pos, neg *)
        | BT (hs,l) ->
          pos,neg
        | PR t ->
          match Term.view t with
          | {Term.f=Symbols.Name(hs,_)} ->
            if is_neg then
              pos, SH.add hs neg
            else
              SH.add hs pos, neg
          | _ -> pos, neg
         ) lits (pos,neg)

  let subst_simpl gfs pos neg =
    let open F in
    let rec aux f =
      match F.view f with
      | Clause (f1,f2,b) ->
        let f1' = aux f1 in
        let f2' = aux f2 in
        if (F.equal f1 f1') && (F.equal f2 f2') then
          f
        else
          F.mk_or f1' f2' b 0
      | Unit (f1,f2) ->
        let f1' = aux f1 in
        let f2' = aux f2 in
        if (F.equal f1 f1') && (F.equal f2 f2') then
          f
        else
          F.mk_and f1' f2' false 0
      | Lemma q ->
        let main = aux q.F.main in
        F.mk_forall
          q.name q.loc q.binders q.triggers main 0 None
      | Skolem q ->
        let main = aux q.F.main in
        F.mk_exists
          q.name q.loc q.binders q.triggers main 0 None
      | Literal l ->
        if replace_with_true l pos neg then
          F.vrai
        else f
      | Flet _| Tlet _ ->
        assert false
    in
    List.rev_map (fun gf ->
        let f = aux gf.F.f in
        if F.equal f gf.F.f then gf else {gf with f =f}
      ) (List.rev gfs)

  let remove_duplicates assumed =
    let seen = SF.singleton F.vrai in
    let _, reduced =
      List.fold_left
        (fun ((seen, reduced) as acc) ({F.f} as gf) ->
          if SF.mem f seen then acc else SF.add f seen, gf :: reduced
        )(seen, []) (List.rev assumed)
    in
    reduced

  let simplify (assumed : F.gformula list) =
    let rec simpl_rec gfs =
      let pos,neg =
        List.fold_left (fun (pos,neg)  gf ->
            get_lits gf (pos,neg)
          ) (SH.empty,SH.empty)  gfs
      in
      let comm = SH.inter pos neg in
      let neg' = SH.diff neg comm in
      let pos' = SH.diff pos comm in
      let gfs' = subst_simpl gfs pos' neg' in
      let fixpoint =
        try List.for_all2 (fun x y -> F.equal x.F.f y.F.f) gfs gfs'
        with _ -> assert false
      in

      if fixpoint then gfs'
      else simpl_rec gfs'
    in
    if debug_sat () then fprintf fmt "In Pur_Literal_PP.simpl_rec@.";
    let assumed2 = simpl_rec assumed in
    if debug_sat () then fprintf fmt "Out Pur_Literal_PP.simpl_rec@.";
    let assumed3 = remove_duplicates assumed2 in
    if debug_sat () then
      fprintf fmt
        "[Pur_Literal_PP.simplify] in with %d facts, out with %d facts@."
        (List.length assumed) (List.length assumed3);
    assumed3

end


module Main (SatCont : Sat_solver_sig.SatContainer)
       : Sat_solver_sig.SatContainer =
  struct

    module Make (Th : Theory.S) : Sat_solver_sig.S = struct

      module SAT = SatCont.Make(Th)

      type t = {
          assumed : F.gformula list;
          pred_def : (F.t * string * Loc.t) list;
          th_axioms: Commands.th_elt list;
          sat : SAT.t
        }

      exception Sat of t
      exception Unsat of Ex.t
      exception I_dont_know of t

      let empty () =
        {
          assumed = [] ;
          pred_def = [];
          th_axioms = [];
          sat = SAT.empty ();
        }

      let empty_with_inst add_inst =
        { (empty ()) with sat = SAT.empty_with_inst add_inst }

      let get_steps () = SAT.get_steps ()

      let reset_refs () = SAT.reset_refs ()

      let print_model ~header fmt env = SAT.print_model ~header fmt env.sat

      let retrieve_used_context env dep = SAT.retrieve_used_context env.sat dep

      let pred_def env f name loc =
        {env with pred_def = (f, name, loc) :: env.pred_def}

      let assume_th_elt env th_elt =
        {env with th_axioms = th_elt :: env.th_axioms}

      let assume env fg =
        { env with assumed = fg :: env.assumed }

      let check_trivial_sat ({ assumed ; pred_def ; th_axioms } as env) =
        if assumed == [] && pred_def == [] && th_axioms == [] then
          raise (Sat env)

      let has_uquantifiers f =
        let open F in
        let rec aux f =
          match view f with
          | Literal _ -> false
          | Lemma _ -> true
          | Skolem {main=f} | Tlet {tlet_f=f} -> aux f
          | Clause (f1, f2, _) | Unit (f1, f2) -> aux f1 || aux f2
          | Flet {flet_f=f1; flet_form=f2} -> aux f1 || aux f2
        in
        aux f

      let check_if_idk_is_sat env sat =
        let is_idk =
          env.pred_def != [] || env.th_axioms != [] ||
            List.exists (fun {F.f} -> has_uquantifiers f) env.assumed
        in
        let env = {sat; assumed = []; pred_def = []; th_axioms = []} in
        raise (if is_idk then I_dont_know env else Sat env)


      let unsat env fg =
        let env = { env with assumed = fg :: env.assumed } in
        let env = { env with assumed = Pur_Literal_PP.simplify env.assumed } in
        check_trivial_sat env;
        try
          let sat =
            List.fold_left
              (fun sat gf -> SAT.assume sat gf)
              env.sat env.assumed
          in
          let sat =
            List.fold_left
              (fun sat (f,name,loc) -> SAT.pred_def sat f name loc)
              sat env.pred_def
          in
          let sat =
            List.fold_left
              (fun sat gf -> SAT.assume_th_elt sat gf)
              sat env.th_axioms
          in
          SAT.unsat sat
            {Formula.f=F.vrai;
             origin_name = "<goal>";
             hdist = -1;
             gdist = 0;
             trigger_depth = max_int;
             nb_reductions = 0;
             age=0;
             lem=None;
	     mf=false;
             gf=true;
             from_terms = [];
             theory_elim = true;
            }
        with
        | SAT.Unsat dep -> dep
        | SAT.I_dont_know sat -> check_if_idk_is_sat env sat
        | SAT.Sat sat ->(*
           fprintf fmt "Are other SATs able to detect Satisfibility ?!";
           assert false*)
          let env = {sat; assumed = []; pred_def = []; th_axioms = []} in
          raise (Sat env)

    end
  end
