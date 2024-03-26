(**************************************************************************)
(*                                                                        *)
(*     Alt-Ergo: The SMT Solver For Software Verification                 *)
(*     Copyright (C) 2013-2023 --- OCamlPro SAS                           *)
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
(*     Until 2013, some parts of this code were released under            *)
(*     the Apache Software License version 2.0.                           *)
(*                                                                        *)
(*     ---------------------------------------------------------------    *)
(*                                                                        *)
(*     More details can be found in the directory licenses/               *)
(*                                                                        *)
(**************************************************************************)

(* To get rid of warnings produced by ppx_deriving. *)
[@@@warning "-32"]

(* The type of modules, followed by the list of every element. *)
type mod_ =
  | M_None
  | M_Typing
  | M_Sat
  | M_Match
  | M_CC
  | M_UF
  | M_Arith
  | M_Arrays
  | M_Sum
  | M_Records
  | M_Adt
  | M_Bitv
  | M_AC
  | M_Expr
  | M_Triggers
  | M_Simplex
  | M_Ite
  | M_Combine
[@@deriving enum]

let all_mod_ =
  let l = [
    M_None;
    M_Typing;
    M_Sat;
    M_Match;
    M_CC;
    M_UF;
    M_Arith;
    M_Arrays;
    M_Sum;
    M_Records;
    M_Adt;
    M_Bitv;
    M_AC;
    M_Expr;
    M_Triggers;
    M_Simplex;
    M_Ite;
    M_Combine
  ]
  in
  assert ((List.length l) = max_mod_ + 1);
  l

let show_mod_ k =
  match k with
  | M_None     -> "None"
  | M_Typing   -> "Typing"
  | M_Sat      -> "Sat"
  | M_Match    -> "Match"
  | M_CC       -> "CC"
  | M_UF       -> "UF"
  | M_Arith    -> "Arith"
  | M_Arrays   -> "Arrays"
  | M_Sum      -> "Sum"
  | M_Records  -> "Records"
  | M_Adt      -> "Adt"
  | M_Bitv     -> "Bitv"
  | M_AC       -> "AC"
  | M_Expr     -> "Expr"
  | M_Triggers -> "Triggers"
  | M_Simplex  -> "Simplex"
  | M_Ite      -> "Ite"
  | M_Combine  -> "Combine"

let parse k =
  match k with
  | "None" -> Some M_None
  | "Typing" -> Some M_Typing
  | "Sat" -> Some M_Sat
  | "Match" -> Some M_Match
  | "CC" -> Some M_CC
  | "UF" -> Some M_UF
  | "Arith" -> Some M_Arith
  | "Arrays" -> Some M_Arrays
  | "Sum" -> Some M_Sum
  | "Records" -> Some M_Records
  | "Adt" -> Some M_Adt
  | "Bitv" -> Some M_Bitv
  | "AC" -> Some M_AC
  | "Expr" -> Some M_Expr
  | "Triggers" -> Some M_Triggers
  | "Simplex" -> Some M_Simplex
  | "Ite" -> Some M_Ite
  | "Combine" -> Some M_Combine
  | _ -> None

let sources =
  Array.init (max_mod_ + 1) (fun i ->
      let mod_ = mod__of_enum i |> Option.get in
      Logs.Src.create ~doc:(show_mod_ mod_)
        ("alt-ergo-lib." ^ (show_mod_ mod_))
    )

let get_source mod_ = sources.(mod__to_enum mod_)

let set_level mod_ lvl = Logs.Src.set_level (get_source mod_) lvl

(* The type of functions, followed by the list of every element. *)
type fn =
  | F_add
  | F_add_lemma
  | F_add_predicate
  | F_add_terms
  | F_are_equal
  | F_assume
  | F_class_of
  | F_leaves
  | F_make
  | F_m_lemmas
  | F_m_predicates
  | F_query
  | F_solve
  | F_subst
  | F_union
  | F_unsat
  | F_none
  | F_new_facts
  | F_apply_subst
  | F_instantiate
  | F_case_split
[@@deriving enum]

let all_fn =
  let l = [
    F_add;
    F_add_lemma;
    F_add_predicate;
    F_add_terms;
    F_are_equal;
    F_assume;
    F_class_of;
    F_leaves;
    F_make;
    F_m_lemmas;
    F_m_predicates;
    F_query;
    F_solve;
    F_subst;
    F_union;
    F_unsat;
    F_none;
    F_new_facts;
    F_apply_subst;
    F_instantiate;
    F_case_split;
  ]
  in
  assert ((List.length l) = max_fn + 1);
  l

let show_fn f =
  match f with
  | F_add           -> "add"
  | F_add_lemma     -> "add_lemma"
  | F_assume        -> "assume"
  | F_class_of      -> "class_of"
  | F_leaves        -> "leaves"
  | F_make          -> "make"
  | F_m_lemmas      -> "m_lemmas"
  | F_m_predicates  -> "m_predicates"
  | F_query         -> "query"
  | F_solve         -> "solve"
  | F_subst         -> "subst"
  | F_union         -> "union"
  | F_unsat         -> "unsat"
  | F_add_predicate -> "add_predicate"
  | F_add_terms     -> "add_terms"
  | F_are_equal     -> "are_equal"
  | F_none          -> "none"
  | F_new_facts     -> "new_facts"
  | F_apply_subst   -> "apply_subst"
  | F_instantiate   -> "instantiate"
  | F_case_split    -> "case_split"

let tag_fn f =
  let s = show_fn f in
  Logs.Tag.def s Fmt.(const string s)
