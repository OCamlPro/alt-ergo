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

open Options
open Format
open Typed
open Commands

module E = Expr
module Sy = Symbols
module SE = E.Set

[@@ocaml.ppwarning "TODO: Change Symbols.Float to store FP numeral \
                    constants (eg, <24, -149> for single) instead of \
                    having terms"]
let make_adequate_app s l ty =
  let open Fpa_rounding in
  match s with
  | Sy.Name (hs, Sy.Other) when Options.get_use_fpa() ->
    let s, l  =
      match Hstring.view hs, l with
      | "float", [_;_;_;_] -> Sy.Op Sy.Float, l
      | "float32", [_;_;] -> Sy.Op Sy.Float,(E.int "24")::(E.int "149")::l
      | "float32d", [_] ->
        Sy.Op Sy.Float,
        (E.int "24")::
        (E.int "149")::
        _NearestTiesToEven__rounding_mode :: l

      | "float64", [_;_;] -> Sy.Op Sy.Float,(E.int "53")::(E.int "1074")::l
      | "float64d", [_] ->
        Sy.Op Sy.Float,
        (E.int "53")::
        (E.int "1074")::
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
    E.mk_term s l ty
  | _ -> E.mk_term s l ty

let varset_of_list =
  List.fold_left
    (fun acc (s,ty) ->
       SE.add (E.mk_term s [] (Ty.shorten ty)) acc) SE.empty

module ME =
  Map.Make
    (struct
      type t = E.t
      let compare a b =
        let c = E.depth a - E.depth b in
        if c <> 0 then c
        else E.compare a b
    end)

(* clean trigger:
   remove useless terms in multi-triggers after inlining of lets*)
let clean_trigger ~in_theory name trig =
  if in_theory then trig
  else
    match trig with
    | [] | [_] -> trig
    | _ ->
      let s =
        List.fold_left
          (fun s t ->
             if ME.mem t s then s
             else
               ME.add t (E.sub_terms SE.empty t) s
          )ME.empty trig
      in
      let res =
        ME.fold
          (fun t _ acc ->
             let rm = ME.remove t acc in
             if ME.exists (fun _ sub -> SE.mem t sub) rm then rm
             else acc
          ) s s
      in
      let sz_l = List.length trig in
      let sz_s = ME.cardinal res in
      if sz_l = sz_s then trig
      else
        let trig' = ME.fold (fun t _ acc -> t :: acc) res [] in
        if get_verbose () then
          Printer.print_dbg ~module_name:"Cnf"
            ~function_name:"clean_trigger"
            "AXIOM: %s@ \
             from multi-trig of sz %d : %a@ \
             to   multi-trig of sz %d : %a"
            name
            sz_l E.print_list trig sz_s E.print_list trig';
        trig'

let concat_chainable p_op p_ty t acc =
  match E.term_view t with
  | Term {E.f; xs; ty; _} ->
    if Symbols.equal p_op f && Ty.equal p_ty ty then
      List.rev_append (List.rev xs) acc
    else
      t :: acc
  | _ -> t :: acc

let rec make_term up_qv quant_basename t =
  let rec mk_term { c = { tt_ty = ty; tt_desc = tt; _ }; _ } =
    let ty = Ty.shorten ty in
    match tt with
    | TTconst Ttrue ->
      E.vrai
    | TTconst Tfalse ->
      E.faux
    | TTconst Tvoid ->
      E.void
    | TTconst (Tint i) ->
      E.int i
    | TTconst (Treal n) ->
      E.real (Num.string_of_num n)
    | TTconst (Tbitv bt) ->
      E.bitv bt ty
    | TTvar s -> E.mk_term s [] ty
    | TTapp (s, l) ->
      make_adequate_app s (List.map mk_term l) ty

    | TTinInterval (e, lb, ub) ->
      assert (ty == Ty.Tbool);
      E.mk_term (Sy.mk_in lb ub) [mk_term e] ty

    | TTmapsTo (x, e) ->
      assert (ty == Ty.Tbool);
      E.mk_term (Sy.mk_maps_to x) [mk_term e] ty

    | TTinfix (t1, s, t2) ->
      begin
        let t2 = mk_term t2 in (*keep old mk_term order -> avoid regression*)
        let t1 = mk_term t1 in
        match s, ty with
        | Sy.Op Sy.Plus, (Ty.Tint | Ty.Treal) ->
          let args = concat_chainable s ty t2 [] in
          let args = concat_chainable s ty t1 args in
          let args = List.fast_sort E.compare args in
          E.mk_term s args ty
        | _ -> E.mk_term s [t1; t2] ty
      end

    | TTprefix ((Sy.Op Sy.Minus) as s, n) ->
      let t1 = if ty == Ty.Tint then E.int "0" else E.real "0"  in
      E.mk_term s [t1; mk_term n] ty
    | TTprefix _ ->
      assert false

    | TTget (t1, t2) ->
      E.mk_term (Sy.Op Sy.Get)
        [mk_term t1; mk_term t2] ty

    | TTset (t1, t2, t3) ->
      let t1 = mk_term t1 in
      let t2 = mk_term t2 in
      let t3 = mk_term t3 in
      E.mk_term (Sy.Op Sy.Set) [t1; t2; t3] ty

    | TTextract (t1, t2, t3) ->
      let t1 = mk_term t1 in
      let t2 = mk_term t2 in
      let t3 = mk_term t3 in
      E.mk_term (Sy.Op Sy.Extract) [t1; t2; t3] ty

    | TTconcat (t1, t2) ->
      E.mk_term (Sy.Op Sy.Concat)
        [mk_term t1; mk_term t2] ty

    | TTdot (t, s) ->
      E.mk_term (Sy.Op (Sy.Access s)) [mk_term t] ty

    | TTrecord lbs ->
      let lbs = List.map (fun (_, t) -> mk_term t) lbs in
      E.mk_term (Sy.Op Sy.Record) lbs ty

    | TTlet (binders, t2) ->
      let binders =
        List.rev_map (fun (s, t1) -> s, mk_term t1)
          (List.rev binders)
      in
      List.fold_left
        (fun acc (sy, e) ->
           E.mk_let sy e acc 0
           [@ocaml.ppwarning "TODO: should introduce fresh vars"]
        )(mk_term t2) binders

    | TTnamed(lbl, t) ->
      let t = mk_term t in
      E.add_label lbl t;
      t

    | TTite(cond, t1, t2) ->
      let cond =
        make_form
          up_qv quant_basename cond Loc.dummy
          ~decl_kind:E.Daxiom (* not correct, but not a problem *)
          ~toplevel:false
      in
      let t1 = mk_term t1 in
      let t2 = mk_term t2 in
      E.mk_ite cond t1 t2 0

    | TTproject (b, t, s) ->
      E.mk_term (Sy.destruct ~guarded:b (Hstring.view s)) [mk_term t] ty

    | TTmatch (e, pats) ->
      let e = make_term up_qv quant_basename e in
      let pats =
        List.rev_map (fun (p, t) ->
            p, make_term up_qv quant_basename t) (List.rev pats)
      in
      E.mk_match e pats

    | TTform e ->
      make_form
        up_qv quant_basename e Loc.dummy
        ~decl_kind:E.Daxiom (* not correct, but not a problem *)
        ~toplevel:false
  in
  mk_term t


and make_trigger ~in_theory name up_qv quant_basename hyp (e, from_user) =
  let content, guard = match e with
    | [{ c = { tt_desc = TTapp(s, t1::t2::l); _ }; _ }]
      when Sy.equal s Sy.fake_eq ->
      let trs = List.filter (fun t -> not (List.mem t l)) [t1; t2] in
      let trs = List.map (make_term up_qv quant_basename) trs in
      let lit =
        E.mk_eq ~iff:true
          (make_term up_qv quant_basename t1)
          (make_term up_qv quant_basename t2)
      in
      trs, Some lit

    | [{ c = { tt_desc = TTapp(s, t1::t2::l); _ }; _ }]
      when Sy.equal s Sy.fake_neq ->
      let trs = List.filter (fun t -> not (List.mem t l)) [t1; t2] in
      let trs = List.map (make_term up_qv quant_basename) trs in
      let lit =
        E.mk_distinct ~iff:true
          [make_term up_qv quant_basename t1;
           make_term up_qv quant_basename t2]
      in
      trs, Some lit

    | [{ c = { tt_desc = TTapp(s, t1::t2::l); _ }; _ }]
      when Sy.equal s Sy.fake_le ->
      let trs = List.filter (fun t -> not (List.mem t l)) [t1; t2] in
      let trs = List.map (make_term up_qv quant_basename) trs in
      let lit =
        E.mk_builtin ~is_pos:true Sy.LE
          [make_term up_qv quant_basename t1;
           make_term up_qv quant_basename t2]
      in
      trs, Some lit

    | [{ c = { tt_desc = TTapp(s, t1::t2::l); _ }; _ }]
      when Sy.equal s Sy.fake_lt ->
      let trs = List.filter (fun t -> not (List.mem t l)) [t1; t2] in
      let trs = List.map (make_term up_qv quant_basename) trs in
      let lit =
        E.mk_builtin ~is_pos:true Sy.LT
          [make_term up_qv quant_basename t1;
           make_term up_qv quant_basename t2]
      in
      trs, Some lit

    | lt -> List.map (make_term up_qv quant_basename) lt, None
  in
  let t_depth =
    List.fold_left (fun z t -> max z (E.depth t)) 0 content in
  (* clean trigger:
     remove useless terms in multi-triggers after inlining of lets*)
  let content = clean_trigger ~in_theory name content in
  { E.content ; guard ; t_depth; semantic = []; (* will be set by theories *)
    hyp; from_user;
  }

and make_form up_qv name_base ~toplevel f loc ~decl_kind : E.t =
  let name_tag = ref 0 in
  let rec mk_form up_qv ~toplevel c id =
    match c with
    | TFatom a ->
      begin match a.c with
        | TAtrue ->
          E.vrai
        | TAfalse ->
          E.faux
        | TAeq [t1;t2] ->
          E.mk_eq ~iff:true
            (make_term up_qv name_base t1)
            (make_term up_qv name_base t2)
        | TApred (t, negated) ->
          let res = make_term up_qv name_base t in
          if negated then E.neg res else res

        | TAneq lt | TAdistinct lt ->
          let lt = List.map (make_term up_qv name_base) lt in
          E.mk_distinct ~iff:true lt
        | TAle [t1;t2] ->
          E.mk_builtin ~is_pos:true Sy.LE
            [make_term up_qv name_base t1;
             make_term up_qv name_base t2]
        | TAlt [t1;t2] ->
          begin match t1.c.tt_ty with
            | Ty.Tint ->
              let one =
                {c = {tt_ty = Ty.Tint;
                      tt_desc = TTconst(Tint "1")}; annot = t1.annot} in
              let tt2 =
                E.mk_term (Sy.Op Sy.Minus)
                  [make_term up_qv name_base t2;
                   make_term up_qv name_base one]
                  Ty.Tint
              in
              E.mk_builtin ~is_pos:true Sy.LE
                [make_term up_qv name_base t1; tt2]
            | _ ->
              E.mk_builtin ~is_pos:true Sy.LT
                [make_term up_qv name_base t1;
                 make_term up_qv name_base t2]
          end
        | TTisConstr (t, lbl) ->
          E.mk_builtin ~is_pos:true (Sy.IsConstr lbl)
            [make_term up_qv name_base t]

        | _ -> assert false
      end

    | TFop(((OPand | OPor | OPxor) as op),[f1;f2]) ->
      let ff1 = mk_form up_qv ~toplevel:false f1.c f1.annot in
      let ff2 = mk_form up_qv ~toplevel:false f2.c f2.annot in
      begin match op with
        | OPand -> E.mk_and ff1 ff2 false id
        | OPor -> E.mk_or ff1 ff2 false id
        | OPxor -> E.mk_xor ff1 ff2 id
        | _ -> assert false
      end
    | TFop(OPimp,[f1;f2]) ->
      let ff1 = mk_form up_qv ~toplevel:false f1.c f1.annot in
      let ff2 = mk_form up_qv ~toplevel:false f2.c f2.annot in
      E.mk_imp ff1 ff2 id
    | TFop(OPnot,[f]) ->
      E.neg @@ mk_form up_qv ~toplevel:false f.c f.annot
    | TFop(OPif, [cond; f2;f3]) ->
      let cond = mk_form up_qv ~toplevel:false cond.c cond.annot in
      let ff2  = mk_form up_qv ~toplevel:false f2.c f2.annot in
      let ff3  = mk_form up_qv ~toplevel:false f3.c f3.annot in
      E.mk_if cond ff2 ff3 id
    | TFop(OPiff,[f1;f2]) ->
      let ff1 = mk_form up_qv ~toplevel:false f1.c f1.annot in
      let ff2 = mk_form up_qv ~toplevel:false f2.c f2.annot in
      E.mk_iff ff1 ff2 id
    | (TFforall qf | TFexists qf) as f ->
      let name =
        if !name_tag = 0 then name_base
        else sprintf "#%s#sub-%d" name_base !name_tag
      in
      incr name_tag;
      let up_qv =
        List.fold_left (fun z (sy,ty) -> Sy.Map.add sy ty z) up_qv qf.qf_bvars
      in
      let qvars = varset_of_list qf.qf_bvars in
      let binders = E.mk_binders qvars in
      (*let upvars = varset_of_list qf.qf_upvars in*)
      let ff =
        mk_form up_qv ~toplevel:false qf.qf_form.c qf.qf_form.annot in

      let hyp =
        List.map (fun f -> mk_form up_qv ~toplevel:false f.c f.annot) qf.qf_hyp
      in
      let in_theory = decl_kind == E.Dtheory in
      let trs =
        List.map
          (make_trigger ~in_theory name up_qv name_base hyp) qf.qf_triggers in
      let func = match f with
        | TFforall _ -> E.mk_forall
        | TFexists _ -> E.mk_exists
        | _ -> assert false
      in
      func name loc binders trs ff id ~toplevel ~decl_kind

    | TFlet(_,binders,lf) ->
      let binders =
        List.rev_map
          (fun (sy, e) ->
             sy,
             match e with
             | TletTerm t -> make_term up_qv name_base t
             | TletForm g -> mk_form up_qv ~toplevel:false g.c g.annot
          )(List.rev binders)
      in
      let res = mk_form up_qv ~toplevel:false lf.c lf.annot in
      List.fold_left
        (fun acc (sy, e) ->
           E.mk_let sy e acc id
           [@ocaml.ppwarning "TODO: should introduce fresh vars"]
        )res binders

    | TFnamed(lbl, f) ->
      let ff = mk_form up_qv ~toplevel:false f.c f.annot in
      E.add_label lbl ff;
      ff

    | TFmatch (e, pats) ->
      let e = make_term up_qv name_base e in
      let pats =
        List.rev_map (fun (p, f) ->
            p, mk_form up_qv ~toplevel:false f.c f.annot)
          (List.rev pats)
      in
      E.mk_match e pats

    | _ -> assert false
  in
  mk_form up_qv ~toplevel f.c f.annot

(* wrapper of function make_form *)
let make_form name f loc ~decl_kind =
  let ff =
    make_form Sy.Map.empty name f loc ~decl_kind ~toplevel:true
  in
  assert (Sy.Map.is_empty (E.free_vars ff Sy.Map.empty));
  let ff = E.purify_form ff in
  if Ty.Svty.is_empty (E.free_type_vars ff) then ff
  else
    let id = E.id ff in
    E.mk_forall name loc Symbols.Map.empty [] ff id ~toplevel:true ~decl_kind

let mk_assume acc f name loc =
  let ff = make_form name f loc ~decl_kind:E.Daxiom in
  {st_decl=Assume(name, ff, true) ; st_loc=loc} :: acc


(* extract defining term of the function or predicate. From the
   transformation of the parsed AST above, the typed AST is either of the
   form:
   - "forall x. defn <-> typed_e", if defn is a pred defn or returns a
     result of type bool
   - "forall x. defn = typed_e", if defn is a function defn whose
     return type is not bool

   where forall x. is optional (like in 'predicate p = q or r')
*)
let defining_term f =
  if get_verbose () then
    Format.eprintf "defining term of %a@." Typed.print_formula f;
  match f.c with
  | TFforall {qf_form={c=TFop(OPiff,[{c=TFatom {c=TApred(d,_);_};_};_]); _}; _}
  | TFforall {qf_form={c=TFatom {c=TAeq[d;_];_}; _}; _}
  | TFop(OPiff,[{c=TFatom {c=TApred(d,_);_};_};_])
  | TFatom {c=TAeq[d;_];_} ->
    d
  | _ -> assert false

let mk_function acc f name loc =
  let defn = defining_term f in
  let defn = make_term Sy.Map.empty "" defn in
  let ff = make_form name f loc ~decl_kind:(E.Dfunction defn) in
  {st_decl=Assume(name, ff, true) ; st_loc=loc} :: acc

let mk_preddef acc f name loc =
  let defn = defining_term f in
  let defn = make_term Sy.Map.empty "" defn in
  let ff = make_form name f loc ~decl_kind: (E.Dpredicate defn) in
  {st_decl=PredDef (ff, name) ; st_loc=loc} :: acc

let mk_query acc n f loc sort =
  let ff = make_form "" f loc ~decl_kind:E.Dgoal in
  {st_decl=Query(n, ff, sort) ; st_loc=loc} :: acc

let make_rule ({rwt_left = t1; rwt_right = t2; rwt_vars} as r) =
  let up_qv =
    List.fold_left (fun z (sy, ty) -> Sy.Map.add sy ty z) Sy.Map.empty rwt_vars
  in
  let s1 = make_term up_qv "" t1 in
  let s2 = make_term up_qv "" t2 in
  assert (E.is_pure s1);
  assert (E.is_pure s2);
  { r with rwt_left = s1; rwt_right = s2 }

let mk_theory acc l th_name extends _loc =
  List.fold_left
    (fun acc e ->
       let loc, ax_name, f, axiom_kind =
         match e.c with
         | TAxiom (loc, name, ax_kd, f) -> loc, name, f, ax_kd
         | _ -> assert false
       in
       let ax_form = make_form ax_name f loc ~decl_kind:E.Dtheory in
       let th_elt = {Expr.th_name; axiom_kind; extends; ax_form; ax_name} in
       {st_decl=ThAssume th_elt ; st_loc=loc} :: acc
    )acc l

let make acc d =
  match d.c with
  | TPush (loc,n) -> {st_decl=Push n; st_loc=loc} :: acc
  | TPop (loc,n) -> {st_decl=Pop n; st_loc=loc} :: acc
  | TTheory(loc, name, ext, l) -> mk_theory acc l name ext loc
  | TAxiom(loc, name, Util.Default, f) -> mk_assume acc f name loc
  | TAxiom(_, _, Util.Propagator, _) -> assert false
  | TRewriting(loc, _, lr) ->
    {st_decl=RwtDef(List.map make_rule lr); st_loc=loc} :: acc
  | TGoal(loc, sort, n, f) -> mk_query acc n f loc sort
  | TPredicate_def(loc, n, _args, f) -> mk_preddef acc f n loc
  | TFunction_def(loc, n, _args, _rety, f) -> mk_function acc f n loc
  | TTypeDecl _ | TLogic _  -> acc


let make_list l = List.fold_left make [] (List.rev l)
