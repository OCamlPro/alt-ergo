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

open Literal

module type S_Term = sig

  include Literal.S with type elt = Term.t

  val vrai : t
  val faux : t

  val apply_subst : Term.subst -> t -> t

  val terms_nonrec : t -> Term.Set.t
  val terms_rec : t -> Term.Set.t
  val ground_terms : t -> Term.Set.t

  val vars_of : t -> Ty.t Symbols.Map.t -> Ty.t Symbols.Map.t
  val is_ground : t -> bool
  val is_in_model : t -> bool

  (*  module SetEq : Set.S with type elt = t * Term.t * Term.t*)
end

module LT : S_Term = struct

  module L = Literal.Make(Term)
  include L

  let vrai = mk_pred Term.vrai false
  let faux = neg vrai

  let apply_subst subst a =
    match view a with
    | Pred (t1, b) ->
      let t1' = Term.apply_subst subst t1 in
      if t1 == t1' then a else mk_pred t1' b

    | Eq (t1, t2) ->
      let t1' = Term.apply_subst subst t1 in
      let t2' = Term.apply_subst subst t2 in
      if t1 == t1' && t2 == t2' then a else mk_eq t1' t2'

    | Distinct (b, lt) ->
      let lt, same = Lists.apply (Term.apply_subst subst) lt in
      if same then a else mk_distinct b lt

    | Builtin (b, n, l) ->
      let l, same = Lists.apply (Term.apply_subst subst) l in
      if same then a else mk_builtin b n l

  let terms_nonrec a =
    List.fold_left (fun z t -> Term.Set.add t z) Term.Set.empty
      (L.elements a)

  let ground_terms a =
    let res = terms_nonrec a in
    let tmp =
      Term.Set.fold
        (fun t acc ->
           if Term.is_ground t then Term.Set.add t acc
           else Term.subterms acc t
        )res Term.Set.empty
    in
    Term.Set.filter Term.is_ground tmp

  let terms_rec a =
    Term.Set.fold
      (fun t z -> Term.subterms z t)(terms_nonrec a) Term.Set.empty

  let vars_of a acc = Term.Set.fold Term.vars_of (terms_nonrec a) acc

  let is_ground a = Term.Set.for_all Term.is_ground (terms_nonrec a)

  let is_in_model l =
    match view l with
    | Eq (t1, t2) ->
      Term.is_in_model t1 || Term.is_in_model t2
    | Distinct (_, tl) | Builtin (_, _, tl) ->
      List.exists Term.is_in_model tl
    | Pred (t1, b) ->
      Term.is_in_model t1

  let apply_subst s a =
    if Options.timers() then
      try
        Timers.exec_timer_start Timers.M_Literal Timers.F_apply_subst;
        let res = apply_subst s a in
        Timers.exec_timer_pause Timers.M_Literal Timers.F_apply_subst;
        res
      with e ->
        Timers.exec_timer_pause Timers.M_Literal Timers.F_apply_subst;
        raise e
    else apply_subst s a

end

