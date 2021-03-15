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

[@@@ocaml.warning "-33"]
open Options

(*** Combination module of Relations ***)

module Rel1 : Sig_rel.RELATION = IntervalCalculus

module Rel2 : Sig_rel.RELATION = Records_rel

module Rel3 : Sig_rel.RELATION = Bitv_rel

module Rel4 : Sig_rel.RELATION = Arrays_rel

module Rel5 : Sig_rel.RELATION = Enum_rel

module Rel6 : Sig_rel.RELATION = Adt_rel

module Rel7 : Sig_rel.RELATION = Ite_rel


open Sig_rel

type t = {
  r1: Rel1.t;
  r2: Rel2.t;
  r3: Rel3.t;
  r4: Rel4.t;
  r5: Rel5.t;
  r6: Rel6.t;
  r7: Rel7.t;
}

let empty classes = {
  r1=Rel1.empty classes;
  r2=Rel2.empty classes;
  r3=Rel3.empty classes;
  r4=Rel4.empty classes;
  r5=Rel5.empty classes;
  r6=Rel6.empty classes;
  r7=Rel7.empty classes;
}

let (|@|) l1 l2 =
  if l1 == [] then l2
  else if l2 == [] then l1
  else List.rev_append l1 l2

let assume env uf sa =
  Options.exec_thread_yield ();
  let env1, { assume = a1; remove = rm1} =
    Rel1.assume env.r1 uf sa in
  let env2, { assume = a2; remove = rm2} =
    Rel2.assume env.r2 uf sa in
  let env3, { assume = a3; remove = rm3} =
    Rel3.assume env.r3 uf sa in
  let env4, { assume = a4; remove = rm4} =
    Rel4.assume env.r4 uf sa in
  let env5, { assume = a5; remove = rm5} =
    Rel5.assume env.r5 uf sa in
  let env6, { assume = a6; remove = rm6} =
    Rel6.assume env.r6 uf sa in
  let env7, { assume = a7; remove = rm7} =
    Rel7.assume env.r7 uf sa in
  {r1=env1; r2=env2; r3=env3; r4=env4; r5=env5; r6=env6; r7=env7},
  { assume = a1 |@| a2 |@| a3 |@| a4 |@| a5 |@| a6 |@| a7;
    remove = rm1 |@| rm2 |@| rm3 |@| rm4 |@| rm5 |@| rm6 |@| rm7}

let assume_th_elt env th_elt dep =
  Options.exec_thread_yield ();
  let env1 = Rel1.assume_th_elt env.r1 th_elt dep in
  let env2 = Rel2.assume_th_elt env.r2 th_elt dep in
  let env3 = Rel3.assume_th_elt env.r3 th_elt dep in
  let env4 = Rel4.assume_th_elt env.r4 th_elt dep in
  let env5 = Rel5.assume_th_elt env.r5 th_elt dep in
  let env6 = Rel6.assume_th_elt env.r6 th_elt dep in
  let env7 = Rel7.assume_th_elt env.r7 th_elt dep in
  {r1=env1; r2=env2; r3=env3; r4=env4; r5=env5; r6=env6; r7=env7}

let query env uf a =
  Options.exec_thread_yield ();
  match Rel1.query env.r1 uf a with
  | Some _ as ans -> ans
  | None ->
    match Rel2.query env.r2 uf a with
    | Some _ as ans -> ans
    | None ->
      match Rel3.query env.r3 uf a with
      | Some _ as ans -> ans
      | None ->
        match Rel4.query env.r4 uf a with
        | Some _ as ans -> ans
        | None ->
          match Rel5.query env.r5 uf a with
          | Some _ as ans -> ans
          | None ->
            match Rel6.query env.r6 uf a with
            | Some _ as ans -> ans
            | None -> Rel7.query env.r7 uf a

let case_split env uf ~for_model =
  Options.exec_thread_yield ();
  let seq1 = Rel1.case_split env.r1 uf ~for_model in
  let seq2 = Rel2.case_split env.r2 uf ~for_model in
  let seq3 = Rel3.case_split env.r3 uf ~for_model in
  let seq4 = Rel4.case_split env.r4 uf ~for_model in
  let seq5 = Rel5.case_split env.r5 uf ~for_model in
  let seq6 = Rel6.case_split env.r6 uf ~for_model in
  let seq7 = Rel7.case_split env.r7 uf ~for_model in
  let l = seq1 |@| seq2 |@| seq3 |@| seq4 |@| seq5 |@| seq6 |@| seq7 in
  List.sort
    (fun (_,_,sz1) (_,_,sz2) ->
       match sz1, sz2 with
       | Th_util.CS(_,sz1), Th_util.CS(_,sz2) -> Numbers.Q.compare sz1 sz2
       | _ -> assert false
    )l


let add env uf r t =
  Options.exec_thread_yield ();
  let r1, eqs1 =Rel1.add env.r1 uf r t in
  let r2, eqs2 =Rel2.add env.r2 uf r t in
  let r3, eqs3 =Rel3.add env.r3 uf r t in
  let r4, eqs4 =Rel4.add env.r4 uf r t in
  let r5, eqs5 =Rel5.add env.r5 uf r t in
  let r6, eqs6 =Rel6.add env.r6 uf r t in
  let r7, eqs7 =Rel7.add env.r7 uf r t in
  {r1;r2;r3;r4;r5;r6;r7;},eqs1|@|eqs2|@|eqs3|@|eqs4|@|eqs5|@|eqs6|@|eqs7


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
  let r7, l7 =
    Rel7.instantiate ~do_syntactic_matching t_match env.r7 uf selector in
  {r1=r1; r2=r2; r3=r3; r4=r4; r5=r5; r6=r6; r7=r7},
  l7 |@| l6 |@| l5 |@| l4 |@| l3 |@| l2 |@| l1

let retrieve_used_context env dep =
  Options.exec_thread_yield ();
  let r1, l1 = Rel1.retrieve_used_context env.r1 dep in
  let r2, l2 = Rel2.retrieve_used_context env.r2 dep in
  let r3, l3 = Rel3.retrieve_used_context env.r3 dep in
  let r4, l4 = Rel4.retrieve_used_context env.r4 dep in
  let r5, l5 = Rel5.retrieve_used_context env.r5 dep in
  let r6, l6 = Rel6.retrieve_used_context env.r6 dep in
  let r7, l7 = Rel7.retrieve_used_context env.r7 dep in
  r7|@| r6 |@| r5 |@| r4 |@| r3 |@| r2 |@| r1,
  l7 |@| l6 |@| l5 |@| l4 |@| l3 |@| l2 |@| l1

let print_model fmt env rs =
  Rel1.print_model fmt env.r1 rs;
  Rel2.print_model fmt env.r2 rs;
  Rel3.print_model fmt env.r3 rs;
  Rel4.print_model fmt env.r4 rs;
  Rel5.print_model fmt env.r5 rs;
  Rel6.print_model fmt env.r6 rs;
  Rel7.print_model fmt env.r7 rs

let new_terms env =
  let t1 = Rel1.new_terms env.r1 in
  let t2 = Rel2.new_terms env.r2 in
  let t3 = Rel3.new_terms env.r3 in
  let t4 = Rel4.new_terms env.r4 in
  let t5 = Rel5.new_terms env.r5 in
  let t6 = Rel6.new_terms env.r6 in
  let t7 = Rel7.new_terms env.r7 in
  Expr.Set.union t1
    (Expr.Set.union t2
       (Expr.Set.union t3
          (Expr.Set.union t4
             (Expr.Set.union t5
                (Expr.Set.union t6 t7)) )))

