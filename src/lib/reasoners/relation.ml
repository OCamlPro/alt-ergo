(**************************************************************************)
(*                                                                        *)
(*     Alt-Ergo: The SMT Solver For Software Verification                 *)
(*     Copyright (C) --- OCamlPro SAS                                     *)
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
(*     ---------------------------------------------------------------    *)
(*                                                                        *)
(*     More details can be found in the directory licenses/               *)
(*                                                                        *)
(**************************************************************************)

module X = Shostak.Combine

(*** Combination module of Relations ***)

module Rel1 : Sig_rel.RELATION = IntervalCalculus

module Rel2 : Sig_rel.RELATION = Records_rel

module Rel3 : Sig_rel.RELATION = Bitv_rel

module Rel4 : Sig_rel.RELATION = Arrays_rel

module Rel5 : Sig_rel.RELATION = Adt_rel

module Rel6 : Sig_rel.RELATION = Ite_rel

(* This value is unused. *)
let timer = Timers.M_None

type t = {
  r1: Rel1.t;
  r2: Rel2.t;
  r3: Rel3.t;
  r4: Rel4.t;
  r5: Rel5.t;
  r6: Rel6.t;
}

let empty uf =
  let r1, doms1 = Rel1.empty uf in
  let r2, doms2 = Rel2.empty (Uf.set_domains uf doms1) in
  let r3, doms3 = Rel3.empty (Uf.set_domains uf doms2) in
  let r4, doms4 = Rel4.empty (Uf.set_domains uf doms3) in
  let r5, doms5 = Rel5.empty (Uf.set_domains uf doms4) in
  let r6, doms6 = Rel6.empty (Uf.set_domains uf doms5) in
  {r1; r2; r3; r4; r5; r6}, doms6

let (|@|) l1 l2 =
  if l1 == [] then l2
  else if l2 == [] then l1
  else List.rev_append l1 l2

let assume env uf sa =
  Options.exec_thread_yield ();
  let env1, doms1, ({ assume = a1; remove = rm1}:_ Sig_rel.result) =
    Timers.with_timer Rel1.timer Timers.F_assume @@ fun () ->
    Rel1.assume env.r1 uf sa
  in
  let env2, doms2, ({ assume = a2; remove = rm2}:_ Sig_rel.result) =
    Timers.with_timer Rel2.timer Timers.F_assume @@ fun () ->
    Rel2.assume env.r2 (Uf.set_domains uf doms1) sa
  in
  let env3, doms3, ({ assume = a3; remove = rm3}:_ Sig_rel.result) =
    Timers.with_timer Rel3.timer Timers.F_assume @@ fun () ->
    Rel3.assume env.r3 (Uf.set_domains uf doms2) sa
  in
  let env4, doms4, ({ assume = a4; remove = rm4}:_ Sig_rel.result) =
    Timers.with_timer Rel4.timer Timers.F_assume @@ fun () ->
    Rel4.assume env.r4 (Uf.set_domains uf doms3) sa
  in
  let env5, doms5, ({ assume = a5; remove = rm5}:_ Sig_rel.result) =
    Timers.with_timer Rel5.timer Timers.F_assume @@ fun () ->
    Rel5.assume env.r5 (Uf.set_domains uf doms4) sa
  in
  let env6, doms6, ({ assume = a6; remove = rm6}:_ Sig_rel.result) =
    Timers.with_timer Rel6.timer Timers.F_assume @@ fun () ->
    Rel6.assume env.r6 (Uf.set_domains uf doms5) sa
  in
  {r1=env1; r2=env2; r3=env3; r4=env4; r5=env5; r6=env6},
  doms6,
  ({ assume = a1 |@| a2 |@| a3 |@| a4 |@| a5 |@| a6;
     remove = rm1 |@| rm2 |@| rm3 |@| rm4 |@| rm5 |@| rm6 }
   : _ Sig_rel.result)

let assume_th_elt env th_elt dep =
  Options.exec_thread_yield ();
  let env1 = Rel1.assume_th_elt env.r1 th_elt dep in
  let env2 = Rel2.assume_th_elt env.r2 th_elt dep in
  let env3 = Rel3.assume_th_elt env.r3 th_elt dep in
  let env4 = Rel4.assume_th_elt env.r4 th_elt dep in
  let env5 = Rel5.assume_th_elt env.r5 th_elt dep in
  let env6 = Rel6.assume_th_elt env.r6 th_elt dep in
  {r1=env1; r2=env2; r3=env3; r4=env4; r5=env5; r6=env6}

let try_query (type a) (module R : Sig_rel.RELATION with type t = a) env uf a
    k =
  match Timers.with_timer R.timer Timers.F_query
    @@ fun () -> R.query env uf a with
  | Some r -> Some r
  | None -> k ()

let query env uf a =
  Options.exec_thread_yield ();
  try_query (module Rel1) env.r1 uf a @@ fun () ->
  try_query (module Rel2) env.r2 uf a @@ fun () ->
  try_query (module Rel3) env.r3 uf a @@ fun () ->
  try_query (module Rel4) env.r4 uf a @@ fun () ->
  try_query (module Rel5) env.r5 uf a @@ fun () ->
  try_query (module Rel6) env.r6 uf a @@ fun () -> None

let case_split env uf ~for_model =
  Options.exec_thread_yield ();
  let seq1 = Rel1.case_split env.r1 uf ~for_model in
  let seq2 = Rel2.case_split env.r2 uf ~for_model in
  let seq3 = Rel3.case_split env.r3 uf ~for_model in
  let seq4 = Rel4.case_split env.r4 uf ~for_model in
  let seq5 = Rel5.case_split env.r5 uf ~for_model in
  let seq6 = Rel6.case_split env.r6 uf ~for_model in
  let splits = [seq1; seq2; seq3; seq4; seq5; seq6] in
  let splits = List.fold_left (|@|) [] splits in
  List.fast_sort
    (fun (_ ,_ , sz1) (_ ,_ , sz2) ->
       match sz1, sz2 with
       | Th_util.CS (_ , sz1), Th_util.CS (_ , sz2) ->
         Numbers.Q.compare sz1 sz2
       | _ -> assert false
    ) splits

let rec optimizing_dispatcher s l =
  match l with
  | [] -> None
  | f :: l ->
    begin match f s with
      | Some u -> Some u
      | None -> optimizing_dispatcher s l
    end

let optimizing_objective env uf o =
  Options.exec_thread_yield ();
  optimizing_dispatcher o [
    Rel1.optimizing_objective env.r1 uf;
    Rel2.optimizing_objective env.r2 uf;
    Rel3.optimizing_objective env.r3 uf;
    Rel4.optimizing_objective env.r4 uf;
    Rel5.optimizing_objective env.r5 uf
  ]

let add env uf r t =
  Options.exec_thread_yield ();
  let r1, doms1, eqs1 =Rel1.add env.r1 uf r t in
  let r2, doms2, eqs2 =Rel2.add env.r2 (Uf.set_domains uf doms1) r t in
  let r3, doms3, eqs3 =Rel3.add env.r3 (Uf.set_domains uf doms2) r t in
  let r4, doms4, eqs4 =Rel4.add env.r4 (Uf.set_domains uf doms3) r t in
  let r5, doms5, eqs5 =Rel5.add env.r5 (Uf.set_domains uf doms4) r t in
  let r6, doms6, eqs6 =Rel6.add env.r6 (Uf.set_domains uf doms5) r t in
  {r1;r2;r3;r4;r5;r6}, doms6, eqs1|@|eqs2|@|eqs3|@|eqs4|@|eqs5|@|eqs6


let instantiate ~do_syntactic_matching t_match env uf selector =
  Options.exec_thread_yield ();
  let r1, l1 =
    Rel1.instantiate ~do_syntactic_matching t_match env.r1 uf selector in
  let r2, l2 =
    Rel2.instantiate ~do_syntactic_matching t_match env.r2 uf selector in
  let r3, l3 =
    Rel3.instantiate ~do_syntactic_matching t_match env.r3 uf selector in
  let r4, l4 =
    Rel4.instantiate ~do_syntactic_matching t_match env.r4 uf selector in
  let r5, l5 =
    Rel5.instantiate ~do_syntactic_matching t_match env.r5 uf selector in
  let r6, l6 =
    Rel6.instantiate ~do_syntactic_matching t_match env.r6 uf selector in
  {r1=r1; r2=r2; r3=r3; r4=r4; r5=r5; r6=r6},
  l6 |@| l5 |@| l4 |@| l3 |@| l2 |@| l1

let new_terms env =
  Rel1.new_terms env.r1
  |> Expr.Set.union @@ Rel2.new_terms env.r2
  |> Expr.Set.union @@ Rel3.new_terms env.r3
  |> Expr.Set.union @@ Rel4.new_terms env.r4
  |> Expr.Set.union @@ Rel5.new_terms env.r5
  |> Expr.Set.union @@ Rel6.new_terms env.r6
