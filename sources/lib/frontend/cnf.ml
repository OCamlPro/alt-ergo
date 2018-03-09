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
open Typed
open Commands

module T = Term
module F = Formula
module A = Literal
module Sy = Symbols

let ale = Hstring.make "<="
let alt = Hstring.make "<"

  [@ocaml.ppwarning "TODO: Change Symbols.Float to store FP numeral \
   constants (eg, <24, -149> for single) instead of having terms"]
let make_adequate_app s l ty =
  let open Fpa_rounding in
  match s with
  | Sy.Name (hs, Sy.Other) when Options.use_fpa() ->
    let s, l  =
      match Hstring.view hs, l with
      | "float", [_;_;_;_] -> Sy.Op Sy.Float, l
      | "float32", [_;_;] -> Sy.Op Sy.Float,(T.int "24")::(T.int "149")::l
      | "float32d", [_] ->
        Sy.Op Sy.Float,
        (T.int "24")::
          (T.int "149")::
          _NearestTiesToEven__rounding_mode :: l

      | "float64", [_;_;] -> Sy.Op Sy.Float,(T.int "53")::(T.int "1074")::l
      | "float64d", [_] ->
        Sy.Op Sy.Float,
        (T.int "53")::
          (T.int "1074")::
          _NearestTiesToEven__rounding_mode :: l

      | "integer_round", [_;_] -> Sy.Op Sy.Integer_round, l

      | "fixed", [_;_;_;_] -> Sy.Op Sy.Fixed, l
      | "sqrt_real", [_] -> Sy.Op Sy.Sqrt_real, l
      | "sqrt_real_default", [_] -> Sy.Op Sy.Sqrt_real_default, l
      | "sqrt_real_excess", [_] -> Sy.Op Sy.Sqrt_real_excess, l
      | "abs_int", [_] ->  Sy.Op Sy.Abs_int, l
      | "abs_real", [_] ->  Sy.Op Sy.Abs_real, l
      | "real_of_int", [_] -> Sy.Op Sy.Real_of_int, l
      | "int_floor", [_] -> Sy.Op Sy.Int_floor, l
      | "int_ceil", [_] -> Sy.Op Sy.Int_ceil, l
      | "max_real", [_;_] -> Sy.Op Sy.Max_real, l
      | "max_int", [_;_] -> Sy.Op Sy.Max_int, l
      | "min_real", [_;_] -> Sy.Op Sy.Min_real, l
      | "min_int", [_;_] -> Sy.Op Sy.Min_int, l
      | "integer_log2", [_] -> Sy.Op Sy.Integer_log2, l
      | "pow_real_int", [_;_] -> Sy.Op Sy.Pow_real_int, l
      | "pow_real_real", [_;_] -> Sy.Op Sy.Pow_real_real, l

      (* should not happend thanks to well typedness *)
      | ("float"
            | "float32"
            | "float32d"
            | "float64"
            | "float64d"
            | "integer_round"
            | "fixed"
            | "sqrt_real"
            | "abs_int"
            | "abs_real"
            | "real_of_int"
            | "int_floor"
            | "int_ceil"
            | "max_real"
            | "max_int"
            | "min_real"
            | "min_int"
            | "integer_log2"
            | "power_of"), _ ->
        assert false
      | _ -> s, l
    in
    T.make s l ty
  | _ -> T.make s l ty

let varset_of_list =
  List.fold_left
    (fun acc (s,ty) ->
      Term.Set.add (Term.make s [] (Ty.shorten ty)) acc) Term.Set.empty

let bound_of_term (t: T.t) =
  let open Symbols in
  let {T.f=f; ty=ty; xs=xs} = T.view t in
  assert (xs == []);
  match f with
  | Var hs | Int hs | Real hs -> hs, ty
  | Name _ | True | False | Void | Bitv _ | Op _ | In _ | MapsTo _ ->
    assert false

let rec make_term {c = { tt_ty = ty; tt_desc = tt }} =
  let ty = Ty.shorten ty in
  match tt with
    | TTconst Ttrue ->
      T.vrai
    | TTconst Tfalse ->
      T.faux
    | TTconst Tvoid ->
      T.void
    | TTconst (Tint i) ->
      T.int i
    | TTconst (Treal n) ->
      T.real (Num.string_of_num n)
    | TTconst (Tbitv bt) ->
      T.bitv bt ty
    | TTvar s ->
      T.make s [] ty
    | TTapp (s, l) ->
      make_adequate_app s (List.map make_term l) ty

    | TTinInterval (e, a, b, c, d) ->
      assert (ty == Ty.Tbool);
      let b, ty_b = bound_of_term (make_term b) in
      let c, ty_c = bound_of_term (make_term c) in
      let lb = Symbols.mk_bound b ty_b ~is_open:a ~is_lower:true in
      let ub = Symbols.mk_bound c ty_c ~is_open:d ~is_lower:false in
      T.make (Symbols.mk_in lb ub) [make_term e] ty

    | TTmapsTo (x, e) ->
      assert (ty == Ty.Tbool);
      T.make (Symbols.mk_maps_to x) [make_term e] ty

    | TTinfix (t1, s, t2) ->
      T.make s [make_term t1;make_term t2] ty
    | TTprefix ((Sy.Op Sy.Minus) as s, n) ->
      let t1 = if ty == Ty.Tint then T.int "0" else T.real "0"  in
      T.make s [t1; make_term n] ty
    | TTprefix _ ->
      assert false
    | TTget (t1, t2) ->
      T.make (Sy.Op Sy.Get) [make_term t1; make_term t2] ty
    | TTset (t1, t2, t3) ->
      let t1 = make_term t1 in
      let t2 = make_term t2 in
      let t3 = make_term t3 in
      T.make (Sy.Op Sy.Set) [t1; t2; t3] ty
    | TTextract (t1, t2, t3) ->
      let t1 = make_term t1 in
      let t2 = make_term t2 in
      let t3 = make_term t3 in
      T.make (Sy.Op Sy.Extract) [t1; t2; t3] ty
    | TTconcat (t1, t2) ->
      T.make (Sy.Op Sy.Concat) [make_term t1; make_term t2] ty
    | TTdot (t, s) ->
      T.make (Sy.Op (Sy.Access s)) [make_term t] ty
    | TTrecord lbs ->
      let lbs = List.map (fun (_, t) -> make_term t) lbs in
      T.make (Sy.Op Sy.Record) lbs ty
    | TTlet (s, t1, t2) ->
      let t1 = make_term t1 in
      let subst = Sy.Map.add s t1 Sy.Map.empty, Ty.esubst in
      let t2 = make_term t2 in
      T.apply_subst subst t2
    | TTnamed(lbl, t) ->
      let t = make_term t in
      T.add_label lbl t;
      t

let make_trigger hyp (e, from_user) =
  let content, guard = match e with
    | [{c={ tt_desc = TTapp(s, t1::t2::l)}}]
        when Sy.equal s Sy.fake_eq ->
      let trs = List.filter (fun t -> not (List.mem t l)) [t1; t2] in
      let trs = List.map make_term trs in
      let lit = A.LT.mk_eq (make_term t1) (make_term t2) in
      trs, Some lit

    | [{c={ tt_desc = TTapp(s, t1::t2::l) } }]
        when Sy.equal s Sy.fake_neq ->
      let trs = List.filter (fun t -> not (List.mem t l)) [t1; t2] in
      let trs = List.map make_term trs in
      let lit = A.LT.mk_distinct false [make_term t1; make_term t2] in
      trs, Some lit

    | [{c={ tt_desc = TTapp(s, t1::t2::l) } }]
        when Sy.equal s Sy.fake_le ->
      let trs = List.filter (fun t -> not (List.mem t l)) [t1; t2] in
      let trs = List.map make_term trs in
      let lit =
        A.LT.mk_builtin true ale [make_term t1; make_term t2]
      in
      trs, Some lit

    | [{c={ tt_desc = TTapp(s, t1::t2::l) } }]
        when Sy.equal s Sy.fake_lt ->
      let trs = List.filter (fun t -> not (List.mem t l)) [t1; t2] in
      let trs = List.map make_term trs in

      let lit =
        A.LT.mk_builtin true alt [make_term t1; make_term t2]
      in
      trs, Some lit

    | lt -> List.map make_term lt, None
  in
  let depth = List.fold_left (fun z t -> max z (T.view t).T.depth) 0 content in
  { F.content ; guard ; depth; semantic = []; (* will be set by theories *)
    hyp; from_user;
  }

let make_form name_base f loc =
  let name_tag = ref 0 in
  let rec make_form toplevel acc c id =
    match c with
    | TFatom a ->
      let a , lit = match a.c with
	| TAtrue ->
	  A.LT.vrai , A.LT.vrai::acc
	| TAfalse ->
	  A.LT.faux , A.LT.faux::acc
	| TAeq [t1;t2] ->
	  let lit = A.LT.mk_eq (make_term t1) (make_term t2) in
	  lit , lit::acc
	| TApred t ->
	  let lit = A.LT.mk_pred (make_term t) false in
	  lit , lit::acc
	| TAneq lt | TAdistinct lt ->
	  let lt = List.map make_term lt in
	  let lit = A.LT.mk_distinct false lt in
	  lit , lit::acc
	| TAle [t1;t2] ->
	  let lit =
	    A.LT.mk_builtin true ale [make_term t1;make_term t2]
	  in lit , lit::acc
 	| TAlt [t1;t2] ->
	  begin match t1.c.tt_ty with
	    | Ty.Tint ->
	      let one =
		{c = {tt_ty = Ty.Tint;
		      tt_desc = TTconst(Tint "1")}; annot = t1.annot} in
	      let tt2 =
		T.make (Sy.Op Sy.Minus)
		  [make_term t2; make_term one] Ty.Tint in
	      let lit =
		A.LT.mk_builtin true ale [make_term t1; tt2]
	      in lit , lit::acc
	    | _ ->
	      let lit =
		A.LT.mk_builtin true alt [make_term t1; make_term t2]
	      in lit, lit::acc
	  end
	| TAbuilt(n,lt) ->
	  let lit = A.LT.mk_builtin true n (List.map make_term lt) in
	  lit , lit::acc
	| _ -> assert false
      in F.mk_lit a id, lit

    | TFop(((OPand | OPor) as op),[f1;f2]) ->
      let ff1 , lit1 = make_form false acc f1.c f1.annot in
      let ff2 , lit2 = make_form false lit1 f2.c f2.annot in
      let mkop = match op with
	| OPand -> F.mk_and ff1 ff2 false id
	| _ -> F.mk_or ff1 ff2 false id in
      mkop , lit2
    | TFop(OPimp,[f1;f2]) ->
      let ff1 , _ = make_form false acc f1.c f1.annot in
      let ff2 , lit = make_form false acc f2.c f2.annot in
      F.mk_imp ff1 ff2 id, lit
    | TFop(OPnot,[f]) ->
      let ff , lit = make_form false acc f.c f.annot in
      F.mk_not ff , lit
    | TFop(OPif t,[f2;f3]) ->
      let tt = make_term t in
      let ff2 , lit2 = make_form false acc f2.c f2.annot in
      let ff3 , lit3 = make_form false lit2 f3.c f3.annot in
      F.mk_if tt ff2 ff3 id, lit3
    | TFop(OPiff,[f1;f2]) ->
      let ff1 , lit1 = make_form false acc f1.c f1.annot in
      let ff2 , lit2 = make_form false lit1 f2.c f2.annot in
      F.mk_iff ff1 ff2 id, lit2
    | (TFforall qf | TFexists qf) as f ->
      let name =
        if !name_tag = 0 then name_base else
          sprintf "#%s#sub-%d" name_base !name_tag
      in
      incr name_tag;
      let qvars = varset_of_list qf.qf_bvars in
      let binders = F.mk_binders qvars in
      (*let upvars = varset_of_list qf.qf_upvars in*)
      let hyp =
        List.map (fun f -> fst (make_form false [] f.c f.annot)) qf.qf_hyp in
      let trs = List.map (make_trigger hyp) qf.qf_triggers in
      let ff , lit = make_form false acc qf.qf_form.c qf.qf_form.annot in
      begin
        match f with
	| TFforall _ ->
          F.mk_forall name loc binders trs ff id None, lit
        | TFexists _ ->
          if toplevel && not (Ty.Set.is_empty (F.type_variables ff)) then
            (* If there is type variables in a toplevel exists:
               1 - we add a forall quantification without term variables
               (ie. only with type variables)
               2 - we keep the triggers of 'exists' to try to instantiate
               type variables with these triggers as guards
            *)
            let nm = sprintf "#%s#sub-%d" name_base 0 in
            let gg = F.mk_exists nm loc binders trs ff id None in
            F.mk_forall name loc Symbols.Map.empty trs gg id None, lit
          else F.mk_exists name loc binders trs ff id None, lit
        | _ -> assert false
      end

    | TFlet(up,lvar,lterm,lf) ->
      let ff, lit = make_form false acc lf.c lf.annot in
      F.mk_let (varset_of_list up) lvar (make_term lterm) ff id, lit

    | TFnamed(lbl, f) ->
      let ff, lit = make_form false acc f.c f.annot in
      F.add_label lbl ff;
      ff, lit

    | _ -> assert false
  in
  make_form true [] f.c f.annot

let mk_assume acc f name loc =
  let ff , _ = make_form name f loc in
  {st_decl=Assume(name, ff, true) ; st_loc=loc} :: acc

let mk_preddef acc f name loc =
  let ff , _ = make_form name f loc  in
  {st_decl=PredDef (ff, name) ; st_loc=loc} :: acc

let mk_query acc n f loc sort =
  let ff, lits = make_form "" f loc in
  {st_decl=Query(n, ff, lits, sort) ; st_loc=loc} :: acc

let make_rule ({rwt_left = t1; rwt_right = t2} as r) =
  { r with rwt_left = make_term t1; rwt_right = make_term t2 }

let mk_theory acc l th_name extends loc =
  List.fold_left
    (fun acc e ->
      let loc, name, f, axiom_kind =
        match e.c with
        | TAxiom (loc, name, ax_kd, f) -> loc, name, f, ax_kd
        | _ -> assert false
      in
      let th_form, _ = make_form name f loc in
      let th_elt = {th_name; axiom_kind; extends; th_form} in
      {st_decl=ThAssume th_elt ; st_loc=loc} :: acc
    )acc l

let make acc d =
  match d.c with
  | TTheory(loc, name, ext, l) -> mk_theory acc l name ext loc
  | TAxiom(loc, name, Parsed.Default, f) ->  mk_assume acc f name loc
  | TAxiom(loc, name, Parsed.Propagator, f) -> assert false
  | TRewriting(loc, name, lr) ->
    {st_decl=RwtDef(List.map make_rule lr); st_loc=loc} :: acc
  | TGoal(loc, sort, n, f) -> mk_query acc n f loc sort
  (*| TPredicate_def(loc, n, [], f) -> mk_preddef acc f n loc b*)
  | TPredicate_def(loc, n, _, f) -> mk_preddef acc f n loc
  | TFunction_def(loc, n, _, _, f) -> mk_assume acc f n loc
  | TTypeDecl _ | TLogic _  -> acc


let make_list l = List.fold_left make [] (List.rev l)
