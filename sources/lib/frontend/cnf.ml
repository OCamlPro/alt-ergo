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

type expr = Term of T.t | Form of F.t * Sy.t * T.t

type let_info = { expr : expr; nb_failed : int ref }

type let_defns = let_info Sy.Map.t

let add_terms_defn binders defns =
  List.fold_left
    (fun defns (x, t) ->
       Sy.Map.add x {expr = Term t ; nb_failed = ref 0} defns
    )defns binders

let add_defns binders defns =
  List.fold_left
    (fun defns (x, e) ->
       Sy.Map.add x {expr = e ; nb_failed = ref 0} defns
    )defns binders

let find_term_defn x defns =
  try match Sy.Map.find x defns with
    | {expr = Term t} -> Some t
    | {expr = Form (f, sy, t) ; nb_failed} ->
      (* we cannot substitute formulas inside terms.
             We will keep corresponding lets *)
      incr nb_failed;
      Some t (* fresh term *)
  with Not_found -> None

let find_any_defn x defns =
  try Some (Sy.Map.find x defns).expr
  with Not_found -> None

let filter_out_fully_replaced binders defns =
  List.filter
    (fun (sy, _) ->
       try !((Sy.Map.find sy defns).nb_failed) <> 0
       with Not_found -> assert false
    ) binders

let remove_defn x defns = Sy.Map.remove x defns

let abstract_form_in_term =
  let cpt = ref 0 in
  fun f abstr ->
    try let _, abstr_t, _ = F.Map.find f !abstr in abstr_t
    with Not_found ->
      incr cpt;
      let fresh_sy = Sy.fresh ~mk_var:true (Hstring.fresh_string()) in
      let fresh_t = T.make fresh_sy [] Ty.Tbool in
      abstr := F.Map.add f (fresh_sy, fresh_t, !cpt) !abstr;
      fresh_t

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

let inline_abstractions in_term parent_abstr abstr up_qv tmp =
  if in_term then tmp
  else
    let id = F.id tmp in
    let l_abstr =
      F.Map.fold
        (fun f e acc ->
           if F.Map.mem f parent_abstr then acc else (f, e) :: acc
        )!abstr []
    in
    let l_abstr =
      List.fast_sort (fun (_,(_,_,x)) (_,(_,_,y)) -> y - x) l_abstr
    in
    abstr := parent_abstr;
    List.fold_left
      (fun acc (f, (sy, t, _)) -> F.mk_let up_qv sy f acc id) tmp l_abstr


let rec make_term up_qv (defns:let_defns) abstr {c = {tt_ty=ty; tt_desc=tt}} =
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
      begin match find_term_defn s defns with
        | Some t -> t
        | None -> T.make s [] ty
      end
    | TTapp (s, l) ->
      make_adequate_app s (List.map (make_term up_qv defns abstr) l) ty

    | TTinInterval (e, a, b, c, d) ->
      assert (ty == Ty.Tbool);
      let b, ty_b = bound_of_term (make_term up_qv defns abstr b) in
      let c, ty_c = bound_of_term (make_term up_qv defns abstr c) in
      let lb = Symbols.mk_bound b ty_b ~is_open:a ~is_lower:true in
      let ub = Symbols.mk_bound c ty_c ~is_open:d ~is_lower:false in
      T.make (Symbols.mk_in lb ub) [make_term up_qv defns abstr e] ty

    | TTmapsTo (x, e) ->
      assert (ty == Ty.Tbool);
      T.make (Symbols.mk_maps_to x) [make_term up_qv defns abstr e] ty

    | TTinfix (t1, s, t2) ->
      T.make s [make_term up_qv defns abstr t1;
                make_term up_qv defns abstr t2] ty

    | TTprefix ((Sy.Op Sy.Minus) as s, n) ->
      let t1 = if ty == Ty.Tint then T.int "0" else T.real "0"  in
      T.make s [t1; make_term up_qv defns abstr n] ty
    | TTprefix _ ->
      assert false

    | TTget (t1, t2) ->
      T.make (Sy.Op Sy.Get)
        [make_term up_qv defns abstr t1; make_term up_qv defns abstr t2] ty

    | TTset (t1, t2, t3) ->
      let t1 = make_term up_qv defns abstr t1 in
      let t2 = make_term up_qv defns abstr t2 in
      let t3 = make_term up_qv defns abstr t3 in
      T.make (Sy.Op Sy.Set) [t1; t2; t3] ty

    | TTextract (t1, t2, t3) ->
      let t1 = make_term up_qv defns abstr t1 in
      let t2 = make_term up_qv defns abstr t2 in
      let t3 = make_term up_qv defns abstr t3 in
      T.make (Sy.Op Sy.Extract) [t1; t2; t3] ty

    | TTconcat (t1, t2) ->
      T.make (Sy.Op Sy.Concat)
        [make_term up_qv defns abstr t1; make_term up_qv defns abstr t2] ty

    | TTdot (t, s) ->
      T.make (Sy.Op (Sy.Access s)) [make_term up_qv defns abstr t] ty

    | TTrecord lbs ->
      let lbs = List.map (fun (_, t) -> make_term up_qv defns abstr t) lbs in
      T.make (Sy.Op Sy.Record) lbs ty

    | TTlet (binders, t2) ->
      let binders =
        List.rev_map (fun (s, t1) -> s, make_term up_qv defns abstr t1)
          (List.rev binders)
      in
      let defns = add_terms_defn binders defns in
      let res = make_term up_qv defns abstr t2 in
      assert (filter_out_fully_replaced binders defns == []);
      res

    | TTnamed(lbl, t) ->
      let t = make_term up_qv defns abstr t in
      T.add_label lbl t;
      t

    | TTite(cond, t1, t2) ->
      let cond = make_form up_qv ~in_term:true defns abstr "" cond Loc.dummy in
      let t_cond = abstract_form_in_term cond abstr in
      let t1 = make_term up_qv defns abstr t1 in
      let t2 = make_term up_qv defns abstr t2 in
      T.make (Sy.name "ite") [t_cond; t1; t2] ty

and make_trigger up_qv (defns:let_defns) abstr hyp (e, from_user) =
  let content, guard = match e with
    | [{c={ tt_desc = TTapp(s, t1::t2::l)}}]
        when Sy.equal s Sy.fake_eq ->
      let trs = List.filter (fun t -> not (List.mem t l)) [t1; t2] in
      let trs = List.map (make_term up_qv defns abstr) trs in
      let lit =
        A.LT.mk_eq
          (make_term up_qv defns abstr t1)
          (make_term up_qv defns abstr t2)
      in
      trs, Some lit

    | [{c={ tt_desc = TTapp(s, t1::t2::l) } }]
        when Sy.equal s Sy.fake_neq ->
      let trs = List.filter (fun t -> not (List.mem t l)) [t1; t2] in
      let trs = List.map (make_term up_qv defns abstr) trs in
      let lit =
        A.LT.mk_distinct false
          [make_term up_qv defns abstr t1; make_term up_qv defns abstr t2]
      in
      trs, Some lit

    | [{c={ tt_desc = TTapp(s, t1::t2::l) } }]
        when Sy.equal s Sy.fake_le ->
      let trs = List.filter (fun t -> not (List.mem t l)) [t1; t2] in
      let trs = List.map (make_term up_qv defns abstr) trs in
      let lit =
        A.LT.mk_builtin true ale
          [make_term up_qv defns abstr t1; make_term up_qv defns abstr t2]
      in
      trs, Some lit

    | [{c={ tt_desc = TTapp(s, t1::t2::l) } }]
        when Sy.equal s Sy.fake_lt ->
      let trs = List.filter (fun t -> not (List.mem t l)) [t1; t2] in
      let trs = List.map (make_term up_qv defns abstr) trs in
      let lit =
        A.LT.mk_builtin true alt
          [make_term up_qv defns abstr t1; make_term up_qv defns abstr t2]
      in
      trs, Some lit

    | lt -> List.map (make_term up_qv defns abstr) lt, None
  in
  let depth = List.fold_left (fun z t -> max z (T.view t).T.depth) 0 content in
  { F.content ; guard ; depth; semantic = []; (* will be set by theories *)
    hyp; from_user;
  }

and make_pred up_qv defns abstr ({c = { tt_ty = ty; tt_desc = tt }} as z) id =
  match tt with
  | TTvar x ->
    begin match find_any_defn x defns with
      | Some (Form (f,_,_)) -> f
      | Some (Term t) -> F.mk_lit (A.LT.mk_pred t false) id
      | None -> F.mk_lit (A.LT.mk_pred (make_term up_qv defns abstr z) false) id
    end
  | _ ->
    F.mk_lit (A.LT.mk_pred (make_term up_qv defns abstr z) false) id

and make_form up_qv ~in_term defns abstr name_base f loc =
  let name_tag = ref 0 in
  let rec mk_form up_qv (defns:let_defns) toplevel c id =
    let parent_abstr = !abstr in
    let tmp = match c with
      | TFatom a ->
        begin match a.c with
	  | TAtrue ->
	    F.vrai
	  | TAfalse ->
	    F.faux
          | TAeq [t1;t2] ->
            F.mk_lit (A.LT.mk_eq (make_term up_qv defns abstr t1)
                        (make_term up_qv defns abstr t2)) id
	  | TApred (t, negated) ->
            let res = make_pred up_qv defns abstr t id in
            if negated then F.mk_not res else res

          | TAneq lt | TAdistinct lt ->
            let lt = List.map (make_term up_qv defns abstr) lt in
            F.mk_lit (A.LT.mk_distinct false lt) id
          | TAle [t1;t2] ->
	    let lit =
              A.LT.mk_builtin true ale
                [make_term up_qv defns abstr t1; make_term up_qv defns abstr t2]
            in
            F.mk_lit lit id
 	  | TAlt [t1;t2] ->
	    begin match t1.c.tt_ty with
	      | Ty.Tint ->
	        let one =
		  {c = {tt_ty = Ty.Tint;
		        tt_desc = TTconst(Tint "1")}; annot = t1.annot} in
	        let tt2 =
		  T.make (Sy.Op Sy.Minus)
                    [make_term up_qv defns abstr t2;
                     make_term up_qv defns abstr one]
                    Ty.Tint
                in
                F.mk_lit
                  (A.LT.mk_builtin true ale
                     [make_term up_qv defns abstr t1; tt2]) id
	      | _ ->
                let lit =
                  A.LT.mk_builtin true alt
                    [make_term up_qv defns abstr t1;
                     make_term up_qv defns abstr t2]
                in
                F.mk_lit lit id
	    end
	  | TAbuilt(n,lt) ->
            F.mk_lit
              (A.LT.mk_builtin true n
                 (List.map (make_term up_qv defns abstr) lt)) id
	  | _ -> assert false
        end

    | TFop(((OPand | OPor | OPxor) as op),[f1;f2]) ->
      let ff1 = mk_form up_qv defns false f1.c f1.annot in
      let ff2 = mk_form up_qv defns false f2.c f2.annot in
      let mkop = match op with
	| OPand -> F.mk_and ff1 ff2 false id
        | OPor -> F.mk_or ff1 ff2 false id
        | OPxor -> F.mk_xor ff1 ff2 false id
        | _ -> assert false
      in
      mkop
    | TFop(OPimp,[f1;f2]) ->
      let ff1 = mk_form up_qv defns false f1.c f1.annot in
      let ff2 = mk_form up_qv defns false f2.c f2.annot in
      F.mk_imp ff1 ff2 id
    | TFop(OPnot,[f]) ->
      let ff = mk_form up_qv defns false f.c f.annot in
      F.mk_not ff
    | TFop(OPif, [cond; f2;f3]) ->
      let cond = mk_form up_qv defns false cond.c cond.annot in
      let ff2  = mk_form up_qv defns false f2.c f2.annot in
      let ff3  = mk_form up_qv defns false f3.c f3.annot in
      F.mk_if cond ff2 ff3 id
    | TFop(OPiff,[f1;f2]) ->
      let ff1 = mk_form up_qv defns false f1.c f1.annot in
      let ff2 = mk_form up_qv defns false f2.c f2.annot in
      F.mk_iff ff1 ff2 id
    | (TFforall qf | TFexists qf) as f ->
      let name =
        if !name_tag = 0 then name_base else
          sprintf "#%s#sub-%d" name_base !name_tag
      in
      incr name_tag;
      let defns =
        List.fold_left (fun defns (x, y) -> remove_defn x defns)
          defns qf.qf_bvars
      in
      let up_qv =
        List.fold_left (fun z (sy,_) -> Sy.Set.add sy z) up_qv qf.qf_bvars
      in
      let qvars = varset_of_list qf.qf_bvars in
      let binders = F.mk_binders qvars in
      (*let upvars = varset_of_list qf.qf_upvars in*)
      let hyp =
        List.map (fun f ->
            mk_form up_qv defns false f.c f.annot) qf.qf_hyp in
      let trs = List.map (make_trigger up_qv defns abstr hyp) qf.qf_triggers in
      let ff = mk_form up_qv defns false qf.qf_form.c qf.qf_form.annot in
      (* for for_all, we should eventually inline some introduced abstractions
         before constructing the quantified formulas *)
      let ff = inline_abstractions in_term parent_abstr abstr up_qv ff in
      begin
        match f with
	| TFforall _ ->
          F.mk_forall name loc binders trs ff id None
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
            F.mk_forall name loc Symbols.Map.empty trs gg id None
          else F.mk_exists name loc binders trs ff id None
        | _ -> assert false
      end

    | TFlet(up,binders,lf) ->
      let binders =
        List.rev_map
          (fun (sy, e) ->
             match e with
               | TletTerm t -> sy, Term (make_term up_qv defns abstr t)
             | TletForm g ->
               let fresh_sy = Sy.fresh ~mk_var:true (Hstring.fresh_string()) in
               let fresh_t = T.make fresh_sy [] Ty.Tbool in
               let gg = mk_form up_qv defns false g.c g.annot in
               sy, Form (gg, fresh_sy, fresh_t)
          )(List.rev binders)
      in
      let defns = add_defns binders defns in
      let res = mk_form up_qv defns false lf.c lf.annot in
      let remaining = filter_out_fully_replaced binders defns in
      if remaining == [] then res
      else
        (* should use F.mk_let: renaming needed to avoid captures when
           transforming let x = ... and y = ... to let x = ... in let
           y = ... *)
        List.fold_left
          (fun acc (sy, e) ->
             match e with
             | Term t ->
               assert false (* should be fully replaced *)
             | Form (gg, sy_gg, t_gg) ->
               (* not sy, but sy_gg, a fresh replacement of sy *)
               F.mk_let up_qv sy_gg gg acc id
          )res remaining

    | TFnamed(lbl, f) ->
      let ff = mk_form up_qv defns false f.c f.annot in
      F.add_label lbl ff;
      ff

    | _ -> assert false
    in
    inline_abstractions in_term parent_abstr abstr up_qv tmp
  in
  mk_form up_qv defns true f.c f.annot

let mk_assume acc f name loc =
  let abstr = ref F.Map.empty in
  let ff =
    make_form Sy.Set.empty ~in_term:false Sy.Map.empty abstr name f loc
  in
  assert (F.Map.is_empty !abstr);
  {st_decl=Assume(name, ff, true) ; st_loc=loc} :: acc

let mk_preddef acc f name loc =
  let abstr = ref F.Map.empty in
  let ff =
    make_form Sy.Set.empty ~in_term:false Sy.Map.empty abstr name f loc
  in
  assert (F.Map.is_empty !abstr);
  {st_decl=PredDef (ff, name) ; st_loc=loc} :: acc

let mk_query acc n f loc sort =
  let abstr = ref F.Map.empty in
  let ff =
    make_form Sy.Set.empty ~in_term:false Sy.Map.empty abstr "" f loc
  in
  assert (F.Map.is_empty !abstr);
  {st_decl=Query(n, ff, sort) ; st_loc=loc} :: acc

let make_rule ({rwt_left = t1; rwt_right = t2; rwt_vars} as r) =
  let up_qv =
    List.fold_left (fun z (sy, _) -> Sy.Set.add sy z) Sy.Set.empty rwt_vars
  in
  let abstr = ref F.Map.empty in
  let s1 = make_term up_qv Sy.Map.empty abstr t1 in
  assert (F.Map.is_empty !abstr);
  let s2 = make_term up_qv Sy.Map.empty abstr t2 in
  assert (F.Map.is_empty !abstr);
  { r with rwt_left = s1; rwt_right = s2 }

let mk_theory acc l th_name extends loc =
  List.fold_left
    (fun acc e ->
      let loc, name, f, axiom_kind =
        match e.c with
        | TAxiom (loc, name, ax_kd, f) -> loc, name, f, ax_kd
        | _ -> assert false
      in
      let abstr = ref F.Map.empty in
      let th_form =
        make_form Sy.Set.empty ~in_term:false Sy.Map.empty abstr name f loc
      in
      assert (F.Map.is_empty !abstr);
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
