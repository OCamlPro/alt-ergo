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


module Make (Th : Theory.S) = struct

  open Options
  open Format

  module E = Expr
  module ME = E.Map
  module SE = E.Set
  module Ex = Explanation
  module Atom = Satml_types.Atom
  module MA = Atom.Map
  module SAT = Satml.Make(Th)
  module PF = Satml_types.Proxy_formula

  type t =
    {sat : SAT.t;
     assumed : SE.t;
     proxies : Atom.atom ME.t;
     inv_proxies : E.t MA.t;
     hcons_env : Atom.hcons_env;
     decisions : (int * E.t) list;
     pending : (E.gformula * Ex.t) list list;
    }

  exception Bottom of Explanation.t * E.Set.t list * t

  let empty () =
    {sat = SAT.empty ();
     assumed = SE.empty;
     proxies = ME.empty;
     inv_proxies = MA.empty;
     hcons_env = Atom.empty_hcons_env ();
     decisions=[];
     pending=[]}

  let formula_of_atom env a =
    try let p = MA.find a env.inv_proxies in p
    with Not_found -> assert false

  let is_true env f =
    match PF.get_proxy_of f env.proxies with
    | Some p ->
      assert (not (Atom.is_true p) || (Atom.level p) >= 0);
      if (Atom.is_true p) then
        let l_ex =
          let r = Atom.Set.fold (fun a acc ->
              SE.add (formula_of_atom env a) acc)
              (SAT.reason_of_deduction p) SE.empty in
          lazy (Ex.make_deps r) in
        Some (l_ex,Atom.level p)
      else None
    | None -> assert false

  let forget_decision env f lvl =
    let l_ok, _ =
      List.partition (fun (dlvl, _) -> dlvl < lvl) env.decisions in
    let env = { env with decisions = l_ok } in
    let a = match PF.get_proxy_of f env.proxies with
      | Some p -> p
      | None -> (* TODO *)
        match PF.get_proxy_of (E.neg f) env.proxies with
        | Some p -> p
        | None -> assert false
    in
    if Atom.reason a == None && Atom.level a > 0 then
      (* right level of f in SAT because of other decisions that may be
         propagated*)
      SAT.cancel_until env.sat ((Atom.level a) - 1);
    env

  let reset_decisions env = SAT.cancel_until env.sat 0;
    {env with decisions = []}

  let get_decisions env = env.decisions

  let decide_aux env (dlvl,f) =
    begin
      match is_true env f, is_true env (E.neg f) with
      | None, None -> begin
          match PF.get_proxy_of f env.proxies  with
          | Some p -> SAT.decide env.sat p
          | None -> assert false
        end
      | Some _, Some _ -> assert false
      | Some _, None ->
        if verbose () && debug_sat () then
          fprintf fmt "!!! [dlvl=%d] %a becomes true before deciding@."
            dlvl E.print f;
      | None, Some (ex, _) ->
        if verbose () && debug_sat () then
          fprintf fmt "!!! [dlvl=%d] %a becomes false before deciding@."
            dlvl E.print f;(* Satml_types.Atom.pr_atom (fst f); *)
        let ex = Ex.union (Ex.singleton (Ex.Bj f)) (Lazy.force ex) in
        raise (Bottom (ex, [], env))
        (*SAT.print_env ();*)
    end

  let assume delay env l =
    let env = {env with pending = l :: env.pending} in
    if delay then env
    else
      let ll = List.rev env.pending in
      let env = {env with pending = []} in
      let env, pfl, cnf, new_vars =
        List.fold_left (fun acc l ->
            List.fold_left
              (fun ((env, pfl, cnf, vars) as acc) ({ E.ff = f; _ }, ex) ->
                 if SE.mem f env.assumed then acc
                 else
                 if Ex.has_no_bj ex then begin
                   let pf, (added_proxy, inv_proxies, new_vars, cnf) =
                     PF.mk_cnf env.hcons_env f
                       (env.proxies, env.inv_proxies, vars, cnf) in
                   {env with assumed = SE.add f env.assumed;
                             proxies = added_proxy; inv_proxies},
                   [pf] :: pfl, cnf, new_vars
                 end
                 else acc
              ) acc l
          )(env, [], [], []) ll
      in
      if pfl != [] then env
      else
        let () =
          try
            let _ =
              SAT.new_vars env.sat ~nbv:(Atom.nb_made_vars env.hcons_env)
                new_vars [] []
            in
            SAT.assume_simple env.sat cnf;
            SAT.assume_simple env.sat pfl;

            List.iter (decide_aux env)
              (List.rev env.decisions);
          with
          | Satml.Sat ->
            assert false
          (* Uncomment if Sat.solve is called *)
          (* SAT.cancel_until env.sat 0;
           * env *)

          | Satml.Unsat _ ->
            assert (Options.tableaux_cdcl () && SAT.decision_level env.sat = 0);
            raise (Bottom (Ex.empty, [], env))

          | Satml.Last_UIP_reason r ->
            let r =
              Atom.Set.fold (fun a acc ->
                  SE.add (formula_of_atom env a) acc) r SE.empty
            in
            raise (Bottom (Ex.make_deps r, [], env))
        in
        env

  let decide env f dlvl =
    try
      decide_aux env (dlvl, f);
      assert (dlvl = List.length env.decisions + 1);
      {env with decisions = (dlvl, f) :: env.decisions}
    with
    | Satml.Unsat _ ->
      assert (Options.tableaux_cdcl () && SAT.decision_level env.sat = 0);
      raise (Bottom (Ex.empty, [], env))

    | Satml.Last_UIP_reason r ->
      let r =
        Atom.Set.fold (fun a acc ->
            SE.add (formula_of_atom env a) acc) r SE.empty
      in
      raise (Bottom (Ex.make_deps r, [], env))
end
