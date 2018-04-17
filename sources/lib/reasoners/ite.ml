(******************************************************************************)
(*                                                                            *)
(*     Alt-Ergo: The SMT Solver For Software Verification                     *)
(*     Copyright (C) 2013-2017 --- OCamlPro SAS                               *)
(*                                                                            *)
(*     This file is distributed under the terms of the license indicated      *)
(*     in the file 'License.OCamlPro'. If 'License.OCamlPro' is not           *)
(*     present, please contact us to clarify licensing.                       *)
(*                                                                            *)
(******************************************************************************)

open Options
open Format
module T  = Term

type 'a abstract = unit

module type ALIEN = sig
  include Sig.X
  val embed : r abstract -> r
  val extract : r -> (r abstract) option
end

module Shostak (X : ALIEN) = struct

  type t = X.r abstract
  type r = X.r

  let name           = "Ite"
  let is_mine_symb _ = false
  let fully_interpreted sb = assert false
  let type_info _    = assert false
  let color _        = assert false
  let print _ _      = assert false
  let embed _        = assert false
  let is_mine _      = assert false
  let compare _ _    = assert false
  let equal _ _      = assert false
  let hash _         = assert false
  let leaves _       = assert false
  let subst _ _ _    = assert false
  let make _         = assert false
  let term_extract _ = None, false
  let abstract_selectors p acc = assert false
  let solve r1 r2 = assert false
  let assign_value r _ eq = assert false
  let choose_adequate_model t _ l = assert false
end

module Relation (X : ALIEN) (Uf : Uf.S) = struct

  open Sig
  module Ex = Explanation

  type r = X.r
  type uf = Uf.t

  module TX2 = struct
    type t = T.t * T.t
    let compare (s1, s2) (t1, t2) =
      let c = T.compare s1 t1 in
      if c <> 0 then c else T.compare s2 t2
  end

  module MT2 = Map.Make(TX2)
  module ST2 = Set.Make(TX2)
  module MT = Term.Map

  module TB =
    Map.Make
      (struct
        type t = T.t * bool
        let compare (a1, b1) (a2, b2) =
          let c = T.compare a1 a2 in
          if c <> 0 then c else Pervasives.compare b1 b2
      end)

  type t =
    { pending_deds      : Ex.t MT2.t;
      guarded_pos_deds  : ST2.t MT.t;
      guarded_neg_deds  : ST2.t MT.t;
      assumed_pos_preds : Ex.t MT.t;
      assumed_neg_preds : Ex.t MT.t;
    }

  let empty _ =
    { pending_deds  = MT2.empty;
      guarded_pos_deds  = MT.empty;
      guarded_neg_deds  = MT.empty;
      assumed_pos_preds = MT.empty;
      assumed_neg_preds = MT.empty;
    }

  let is_ite =
    let ite = Hstring.make "ite" in
    fun t ->
      match T.view t with
      | {T.f = Symbols.Name(hs, _); xs=[p;t1;t2]} when Hstring.equal ite hs ->
        Some (p, t1, t2)
      | _ ->
        None

  let add_to_guarded p s t mp =
    let st = try MT.find p mp with Not_found -> ST2.empty in
    MT.add p (ST2.add (s, t) st) mp

  let add env _ r t =
    if Options.disable_ites () then env
    else
      match is_ite t with
      | None -> env
      | Some (p, t1, t2) ->
        if debug_ite () then
          fprintf fmt "[Ite.add]: (if %a then %a else %a)@."
            T.print p T.print t1 T.print t2;
        try
          let ex = MT.find p env.assumed_pos_preds in
          {env with pending_deds = MT2.add (t, t1) ex env.pending_deds}
        with Not_found ->
        try
          let ex = MT.find p env.assumed_neg_preds in
          {env with pending_deds = MT2.add (t, t2) ex env.pending_deds}
        with Not_found ->
          let guarded_pos_deds = add_to_guarded p t t1 env.guarded_pos_deds in
          let guarded_neg_deds = add_to_guarded p t t2 env.guarded_neg_deds in
          {env with guarded_pos_deds; guarded_neg_deds}


  let extract_preds env la =
    List.fold_left
      (fun acc (_ra, root, expl, _orig) ->
         match root with
         | None -> acc
         | Some a ->
           match Literal.LT.view a with
           | Literal.Pred (t, is_neg)
             when not (MT.mem t env.assumed_pos_preds) &&
                  not (MT.mem t env.assumed_neg_preds) ->
             if debug_ite () then
               fprintf fmt "[Ite.assume] %a@." Literal.LT.print a;
             TB.add (t, is_neg) expl acc
           | _ -> acc
      )TB.empty la


  let extract_pending_deductions env =
    let l =
      MT2.fold
        (fun (s, t) ex acc ->
           let a = Literal.LT.mk_eq s t in
           if debug_ite () then
             fprintf fmt "[Ite.assume] deduce that %a with expl %a@."
               Literal.LT.print a Ex.print ex;
           (LTerm a, ex, Sig.Other) :: acc)
        env.pending_deds []
    in
    {env with pending_deds = MT2.empty}, l

  let assume env uf la =
    if Options.disable_ites () then env, { assume = []; remove = [] }
    else
      let env =
        TB.fold
          (fun (t, is_neg) ex env ->
             if is_neg then
               let assumed_neg_preds = MT.add t ex env.assumed_neg_preds in
               let deds =
                 try MT.find t env.guarded_neg_deds
                 with Not_found -> ST2.empty
               in
               let pending_deds =
                 ST2.fold (fun e acc -> MT2.add e ex acc) deds env.pending_deds
               in
               {env with assumed_neg_preds; pending_deds}
             else
               let assumed_pos_preds = MT.add t ex env.assumed_pos_preds in
               let deds =
                 try MT.find t env.guarded_pos_deds
                 with Not_found -> ST2.empty
               in
               let pending_deds =
                 ST2.fold (fun e acc -> MT2.add e ex acc) deds env.pending_deds
               in
               {env with assumed_pos_preds; pending_deds}
          )(extract_preds env la) env
      in
      let env, deds = extract_pending_deductions env in
      env, { assume = deds; remove = [] }

  let assume env uf la =
    if Options.timers() then
      try
	Timers.exec_timer_start Timers.M_Arrays Timers.F_assume;
	let res =assume env uf la in
	Timers.exec_timer_pause Timers.M_Arrays Timers.F_assume;
	res
      with e ->
	Timers.exec_timer_pause Timers.M_Arrays Timers.F_assume;
	raise e
    else assume env uf la

  let case_split env uf ~for_model = []

  let query _ _ _ = Sig.No
  let print_model _ _ _ = ()

  let new_terms env = T.Set.empty
  let instantiate ~do_syntactic_matching _ env uf _ = env, []
  let retrieve_used_context _ _ = [], []

  let assume_th_elt t th_elt = t

end
