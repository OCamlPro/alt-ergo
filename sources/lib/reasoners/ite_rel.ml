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

open Options
open Format
module E = Expr

module Ex = Explanation

module EX2 = struct
  type t = E.t * E.t
  let compare (s1, s2) (t1, t2) =
    let c = E.compare s1 t1 in
    if c <> 0 then c else E.compare s2 t2
end

module ME2 = Map.Make(EX2)
module SE2 = Set.Make(EX2)
module ME = Expr.Map

module TB =
  Map.Make
    (struct
      type t = E.t * bool
      let compare (a1, b1) (a2, b2) =
        let c = E.compare a1 a2 in
        if c <> 0 then c else Pervasives.compare b1 b2
    end)

type t =
  { pending_deds      : Ex.t ME2.t;
    guarded_pos_deds  : SE2.t ME.t;
    guarded_neg_deds  : SE2.t ME.t;
    assumed_pos_preds : Ex.t ME.t;
    assumed_neg_preds : Ex.t ME.t;
  }

let empty _ =
  { pending_deds  = ME2.empty;
    guarded_pos_deds  = ME.empty;
    guarded_neg_deds  = ME.empty;
    assumed_pos_preds = ME.empty;
    assumed_neg_preds = ME.empty;
  }

let is_ite =
  let ite = Symbols.Op Symbols.Tite in
  fun t ->
    match E.term_view t with
    | E.Not_a_term _ -> assert false
    | E.Term { E.f ; xs = [p;t1;t2]; _ } when Symbols.equal f ite ->
      Some (p, t1, t2)
    | _ ->
      None

let add_to_guarded p s t mp =
  let st = try ME.find p mp with Not_found -> SE2.empty in
  ME.add p (SE2.add (s, t) st) mp

let add env _ _ t =
  if Options.disable_ites () then env
  else
    match is_ite t with
    | None -> env
    | Some (p, t1, t2) ->
      if debug_ite () then
        fprintf fmt "[Ite.add]: (if %a then %a else %a)@."
          E.print p E.print t1 E.print t2;
      try
        let ex = ME.find p env.assumed_pos_preds in
        {env with pending_deds = ME2.add (t, t1) ex env.pending_deds}
      with Not_found ->
      try
        let ex = ME.find p env.assumed_neg_preds in
        {env with pending_deds = ME2.add (t, t2) ex env.pending_deds}
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
         match E.lit_view a with
         | E.Pred (t, is_neg)
           when not (ME.mem t env.assumed_pos_preds) &&
                not (ME.mem t env.assumed_neg_preds) ->
           if debug_ite () then
             fprintf fmt "[Ite.assume] %a@." E.print a;
           TB.add (t, is_neg) expl acc
         | _ -> acc
    )TB.empty la


let extract_pending_deductions env =
  let l =
    ME2.fold
      (fun (s, t) ex acc ->
         let a = E.mk_eq ~iff:false s t
             [@ocaml.ppwarning "TODO: build IFF instead ?"]
         in
         if debug_ite () then
           fprintf fmt "[Ite.assume] deduce that %a with expl %a@."
             E.print a Ex.print ex;
         (Sig_rel.LTerm a, ex, Th_util.Other) :: acc)
      env.pending_deds []
  in
  {env with pending_deds = ME2.empty}, l

let assume env _ la =
  if Options.disable_ites () then env, { Sig_rel.assume = []; remove = [] }
  else
    let env =
      TB.fold
        (fun (t, is_neg) ex env ->
           if is_neg then
             let assumed_neg_preds = ME.add t ex env.assumed_neg_preds in
             let deds =
               try ME.find t env.guarded_neg_deds
               with Not_found -> SE2.empty
             in
             let pending_deds =
               SE2.fold (fun e acc -> ME2.add e ex acc) deds env.pending_deds
             in
             {env with assumed_neg_preds; pending_deds}
           else
             let assumed_pos_preds = ME.add t ex env.assumed_pos_preds in
             let deds =
               try ME.find t env.guarded_pos_deds
               with Not_found -> SE2.empty
             in
             let pending_deds =
               SE2.fold (fun e acc -> ME2.add e ex acc) deds env.pending_deds
             in
             {env with assumed_pos_preds; pending_deds}
        )(extract_preds env la) env
    in
    let env, deds = extract_pending_deductions env in
    env, { Sig_rel.assume = deds; remove = [] }

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

let case_split _ _ ~for_model:_ = []

let query _ _ _ = None
let print_model _ _ _ = ()

let new_terms _ = E.Set.empty
let instantiate ~do_syntactic_matching:_ _ env _ _ = env, []

let assume_th_elt t _ _ = t

