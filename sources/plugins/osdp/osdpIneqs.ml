(*
 * OSDP (OCaml SDP) plugin for Alt-Ergo
 * Copyright (C) 2018, ONERA
 *
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published by
 * the Free Software Foundation; either version 3 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
 *)

module Container : PolynomialInequalities.Container_SIG = struct
  module Make
    (X : Sig.X)
    (Uf : Uf.S with type r = X.r)
    (P : Polynome.EXTENDED_Polynome with type r = X.r)
    : PolynomialInequalities.S with module P = P = struct

    module Q = Numbers.Q

    module P = P

    module I = Intervals

    module MX0 = Map.Make(struct type t = X.r let compare = X.hash_cmp end)
    
    module Sos = Osdp.Sos.Q
    module SosP = Sos.Poly

    module SSosP = Set.Make (SosP)
    module SSSosP = Set.Make (SSosP)

    module MSSosP = Map.Make
        (struct type t = SSosP.t let compare = SSosP.compare end)
    
    let cache_polynomes = ref MSSosP.empty

    let cache_entry_of pge =
      let pge = List.map fst pge in
      let set_of polys = List.fold_right SSosP.add polys SSosP.empty in
      set_of pge
    let find_res_in_cache ce = MSSosP.find ce !cache_polynomes
    let add_res_to_cache ce res =
      cache_polynomes := MSSosP.add ce res !cache_polynomes

    let p_to_osdp p =
      let combine_opt_env f ft2 opt1 t2 = match opt1 with
        | None -> None
        | Some (t1, env, next) ->
          match ft2 t2 env next with
          | None -> None
          | Some (t2, env, next) -> Some (f t1 t2, env, next) in
      let rec trans_monom t env next = match Term.view t with
        | { Term.f = Symbols.Op Symbols.Mult ; Term.xs = l ; _ } ->
          List.fold_left
            (combine_opt_env SosP.mult trans_monom)
            (Some (SosP.one, env, next)) l
        | _ ->
          let v, env, next =
            try Term.Map.find t env, env, next
            with Not_found -> next, Term.Map.add t next env, next + 1 in
          Some (SosP.var v, env, next) in
      let trans_monom m env next =
        match X.term_extract m with
        | None, _ -> None
        | Some t, _ -> trans_monom t env next in
      let opt =
        let pm, pc = P.to_list p in
        List.fold_left
          (fun opt (c, m) ->
             combine_opt_env
               (fun t1 t2 -> SosP.(add t1 (mult_scalar (Q.to_zarith c) t2)))
               trans_monom opt m)
          (Some (SosP.const (Q.to_zarith pc), Term.Map.empty, 0)) pm in
      match opt with
      | None -> None
      | Some (p, env, _) -> Some (p, env)

    let tr_polys polys =
      try
        List.map
          (fun (p, i) ->
             match p_to_osdp p with
             | None -> raise Exit
             | Some (p, env) -> (p, i), env)
          polys
      with Exit -> []

    (* For a list [polys] of pairs [pi, env] with [env] a mapping from
       terms, [partition polys] returns a list of lists [l] such that
       [pi, env] in differents lists [l] have [env] with empty
       intersection. *)
    let partition polys =
      let uf =
        List.fold_left
          (fun uf (_, env) ->
             match Term.Map.bindings env with
             | [] -> uf
             | (t, _) :: env ->
               let uf, _ = Uf.add uf t in
               let r, _ = Uf.find uf t in
               List.fold_left
                 (fun uf (t', _) ->
                    let uf, _ = Uf.add uf t' in
                    let r', _ = Uf.find uf t' in
                    fst (Uf.union uf r r' Explanation.empty))
                 uf env)
          (Uf.empty ()) polys in
      List.fold_left
        (fun m (pi, env) ->
           try
             let t, _ = Term.Map.choose env in
             let r, _ = Uf.find uf t in
             let l = try MX0.find r m with Not_found -> [] in
             MX0.add r ((pi, env) :: l) m
           with Not_found -> m)
        MX0.empty polys
      |> MX0.bindings |> List.map snd

    (* For a list [polys] of pairs [(p, i), env] with [p] a polynomial
       and [env] a mapping from terms to variable indices in [p],
       [merge polys] returns a list of polynomials using the same
       variable indices for the same symbols. *)
    let merge polys =
      (* For [env] and [env'] mappings from terms to integer indices,
         [merge_env env env'] returns a pair [env'', trans]. [env'']
         contains the same mapping as [env] plus mapping for extra
         variables in [env'] to new indices (not appearing in
         [env]). [trans] is an array of integer indices such that
         [trans.(i) = j] for each variable mapped to [i] in [env'] and
         to [j] in [env'']. *)
      let merge_env env env' =
        let next, trans =
          let sz e = 1 + Term.Map.fold (fun _ -> max) e (-1) in
          sz env, Array.make (sz env') 0 in
        let env'', _ =
          Term.Map.fold
            (fun v i (env, next) ->
               let j, env, next =
                 try Term.Map.find v env, env, next
                 with Not_found -> next, Term.Map.add v next env, next + 1 in
               trans.(i) <- j;
               env, next)
            env' (env, next) in
        env'', trans in
      let apply_trans p trans =
        let trans = Array.to_list trans |> List.map SosP.var in
        SosP.compose p trans in
      let polys, _ =
        List.fold_left
          (fun (polys, env) ((p, i), env') ->
             let env, trans = merge_env env env' in
             (apply_trans p trans, i) :: polys, env)
          ([], Term.Map.empty) polys in
      List.rev polys

    (* For a list of polynomials and intervals [p_i, i_i], returns a
       list [lpge0] of pairs [lpge0_i, e_i] such that \forall i, p_i
       \in i_i implies \forall j, lpge0_j >= 0. [e_i] are explanations
       for lpge0_i >= 0 *)
    let pi_to_pge0 pil =
      let pil = List.filter (fun (_, i) -> I.is_point i = None) pil in
      let d = List.fold_left (fun d (p, _) -> max d (SosP.degree p)) 0 pil in
      let lpe =
        List.map
          (fun (p, i) ->
             let l =
               try let v, ex, _ = I.borne_inf i in Some (Q.to_zarith v, ex)
               with I.No_finite_bound -> None in
             let u =
               try let v, ex, _ = I.borne_sup i in Some (Q.to_zarith v, ex)
               with I.No_finite_bound -> None in
             (* normalize polynomials so that all coeffs are less than 1 *)
             let c =
               SosP.to_list p
               |> List.map (fun (_, n) -> Q.of_zarith n |> Q.abs)
               |> List.fold_left Q.max Q.zero |> Q.to_zarith in
             match l, u with
             | None, None -> []
             | None, Some (u, e) -> SosP.([(!u - p) / c, e])
             | Some (l, e), None -> SosP.([(p - !l) / c, e])
             | Some (l, el), Some (u, eu) ->
               let pl, pu = SosP.((p - !l) / c, (!u - p) / c) in
               if SosP.degree p > d / 2 then [(pl, el); (pu, eu)]
               else [SosP.(pl * pu), Explanation.union el eu])
          pil in
      List.flatten lpe

    (* For a list of polynomials [pge0_i], returns true iff it manages
       to prove that the semi-algebraic set { x \in \R^n | \forall i
       pge0_i >= 0 } is empty. *)
    let psatz pge0 =
      let pge0, expls = List.split pge0 in
      let has_null_const p =
        let zeros =
          SosP.(Array.to_list (Array.make (nb_vars p) Coeff.zero)) in
        SosP.(Coeff.compare (eval p zeros) Coeff.zero = 0) in
      (* if none of pge0 has a constant, 0 satisfies the constraints *)
      if List.for_all has_null_const pge0 then None else
        try
          let get_wits keep =
            let sum, sigmas =
              let n = List.map SosP.nb_vars pge0 |> List.fold_left max 0 in
              let degs = List.map SosP.degree pge0 in
              let max_deg = List.fold_left max 0 degs in
              let rec prod i j = if i > j then 1 else i * prod (i + 1) j in
              let among k n =
                if k > n / 2 then prod (k + 1) n / prod 1 (n - k)
                else prod (n - k + 1) n / prod 1 k in
              (* Format.printf *)
              (*   "n = %d, max_deg = %d, (n parmi n + (d+1)/2) = %d@." *)
              (*   n max_deg (among n (n + (max_deg + 1) / 2)); *)
              if among n (n + (max_deg + 1) / 2) > 64 then raise Exit;
              let max_deg_list =
                pge0 |> List.map SosP.degree_list
                |> List.map Osdp.Monomial.of_list
                |> Osdp.Monomial.(List.fold_left lcm one) in
              let rup n = (n + 1) / 2 * 2 in
              let rup_monomial m =
                Osdp.Monomial.(m |> to_list |> List.map rup |> of_list) in
              List.fold_left
                (fun (sum, sigmas) (p, d) ->
                   let s =
                     let l =
                       let d = max_deg - d in
                       let d = if keep then d else rup d in
                       Sos.make ~n ~d "s" |> Sos.to_list in
                     let l =
                       if keep then l else
                         let lim =
                           let pl =
                             Osdp.Monomial.of_list (SosP.degree_list p) in
                           rup_monomial (Osdp.Monomial.div max_deg_list pl) in
                         List.filter
                           (fun (m, _) -> Osdp.Monomial.divide m lim)
                           l in
                     Sos.of_list l in
                   (* Format.printf "p = %a ~~> s = %a@." Sos.Poly.pp p Sos.pp s; *)
                   Sos.(sum - s * !!p), s :: sigmas)
                (Sos.(!!Poly.zero), []) (List.combine pge0 degs) in
            (* Format.printf "sum: %a@." Sos.pp sum; *)
                          (* Format.printf "degrees: @[%a@]@." (Osdp.Utils.pp_list ~sep:",@ " (fun fmt p -> Format.fprrintf \
                             fmt "%d" (Sos.degree p))) sigmas; *)
            let ret, _, _, witnesses =
              let options =
                { Sos.default
                  with Sos.verbose = 0(*3*) ;
                       Sos.sdp =
                         { Osdp.Sdp.default
                           with Osdp.Sdp.verbose = 0(*1*) } } in
              Sos.solve ~options ~solver:Osdp.Sdp.Csdp
                Sos.Purefeas (sum :: sigmas) in
            match ret, witnesses with
            | Osdp.SdpRet.Success, (m, _) :: _
              when
                (* check that we proved sum > 0 (and not just sum >= 0) *)
                Array.length m > 0 && Osdp.Monomial.(compare m.(0) one) = 0 ->
              Some Explanation.(List.fold_left union empty expls)
            | _ -> None in
          match get_wits false with
          | Some e -> Some e
          | None -> get_wits true
        with Exit -> None

    let psatz pge0 =
      if Options.timers() then
        try
          Timers.exec_timer_start Timers.M_Arith Timers.F_osdp;
          let res = psatz pge0 in
          Timers.exec_timer_pause Timers.M_Arith Timers.F_osdp;
          res
        with e ->
          Timers.exec_timer_pause Timers.M_Arith Timers.F_osdp;
          raise e
      else psatz pge0

    let test_polynomes polys =
      let polys = tr_polys polys in
      let polys = partition polys in
      if Options.debug_sdp () then
        Format.printf "[sdp] %d partition(s)@." (List.length polys);
      polys
      |> List.iter
      (fun polys ->
         (* we don't do anything when everything is linear *)
         if List.exists (fun ((p, _), _) -> SosP.degree p > 1) polys then
           let polys = merge polys in
           let pge0 = pi_to_pge0 polys in
           let ce = cache_entry_of pge0 in
           let res =
             try
               let tmp = find_res_in_cache ce in
               if Options.debug_sdp () then
                 Format.fprintf Options.fmt "[sdp] reuse result in cache@.";
               tmp
             with Not_found ->
               if Options.debug_sdp () then begin
                 Format.fprintf Options.fmt "[sdp] new problem@.";
                 Format.fprintf Options.fmt
                   "[sdp] @[<v>%a@]@."
                   (Osdp.Utils.pp_list
                      ~sep: ",@ "
                      (fun fmt (p, _) ->
                         Format.fprintf Options.fmt "%a >= 0" SosP.pp p))
                   pge0;
               end;
               let tmp = psatz pge0 in
               add_res_to_cache ce tmp;
               tmp
           in
           match res with None -> () | Some expls ->
             if Options.debug_sdp () then Format.printf "[sdp] Inconsistent@.";
             raise (I.NotConsistent expls)
      )
  end
end

let () =
  PolynomialInequalities.set_current
    (module Container : PolynomialInequalities.Container_SIG)
